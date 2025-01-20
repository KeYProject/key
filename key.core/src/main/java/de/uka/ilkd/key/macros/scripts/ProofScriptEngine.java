/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.builder.BuilderHelpers;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.parsing.BuildingIssue;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.misc.Interval;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Consumer;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
public class ProofScriptEngine {
    public static final int KEY_START_INDEX_PARAMETER = 2;

    private static final String SYSTEM_COMMAND_PREFIX = "@";
    private static final int MAX_CHARS_PER_COMMAND = 80;
    private static final Map<String, ProofScriptCommand<? extends Object>> COMMANDS = loadCommands();
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofScriptEngine.class);


    private final KeyAst.ProofScript script;

    /**
     * The initially selected goal.
     */
    private final Goal initiallySelectedGoal;

    /**
     * The engine state map.
     */
    private EngineState stateMap;

    private Consumer<Message> commandMonitor;

    public ProofScriptEngine(File file) throws IOException {
        this.script = Files.readString(file.toPath());
        this.initiallySelectedGoal = null;
    }

    public ProofScriptEngine(KeyAst.ProofScript script) {
        this(script, null);
    }

    /**
     * Instantiates a new proof script engine.
     *
     * @param script                the script
     * @param initiallySelectedGoal the initially selected goal
     */
    public ProofScriptEngine(KeyAst.ProofScript script, Goal initiallySelectedGoal) {
        this.script = script;
        this.initiallySelectedGoal = initiallySelectedGoal;
    }

    private static Map<String, ProofScriptCommand<?>> loadCommands() {
        Map<String, ProofScriptCommand<?>> result = new HashMap<>();
        var loader = ServiceLoader.load(ProofScriptCommand.class);

        for (ProofScriptCommand<?> cmd : loader) {
            result.put(cmd.getName(), cmd);
        }

        return result;
    }

    @SuppressWarnings("unchecked")
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof)
            throws IOException, InterruptedException, ScriptException {
        var ctx = ParsingFacade.getParseRuleContext(script);

        stateMap = new EngineState(proof);

        if (initiallySelectedGoal != null) {
            stateMap.setGoal(initiallySelectedGoal);
        }

        // add the filename (if available) to the statemap.
        URL url = script.getUrl();
        try {
            stateMap.setBaseFileName(Paths.get(url.toURI()).toFile());
        } catch (URISyntaxException e) {
            throw new IOException(e);
        }

        // add the observer (if installed) to the state map
        if (commandMonitor != null) {
            stateMap.setObserver(commandMonitor);
        }


        int cnt = 0;
        for (KeYParser.ProofScriptCommandContext commandContext : ctx.proofScriptCommand()) {
            if (Thread.interrupted()) {
                throw new InterruptedException();
            }

            var argMap = getArguments(commandContext);

            String name = commandContext.cmd.getText();

            String cmd = "'" + argMap.get(ScriptLineParser.LITERAL_KEY) + "'";
            if (cmd.length() > MAX_CHARS_PER_COMMAND) {
                cmd = cmd.substring(0, MAX_CHARS_PER_COMMAND) + " ...'";
            }

            final Node firstNode = stateMap.getFirstOpenAutomaticGoal().node();
            if (commandMonitor != null
                    && stateMap.isEchoOn()
                    && commandContext.AT() == null) {
                commandMonitor
                        .accept(new ExecuteInfo(cmd, start, firstNode.serialNr()));
            }

            try {
                ProofScriptCommand<Object> command =
                    (ProofScriptCommand<Object>) COMMANDS.get(name);
                if (command == null) {
                    throw new ScriptException("Unknown command " + name + " at "
                            + BuilderHelpers.getPosition(commandContext));
                }

                Object o = command.evaluateArguments(stateMap, argMap);
                if (commandContext.AT() == null && stateMap.isEchoOn()) {
                    LOGGER.debug("[{}] goal: {}, source line: {}, command: {}", ++cnt,
                        firstNode.serialNr(), parsed.start().getPosition().line(), cmd);
                }
                command.execute(uiControl, o, stateMap);
                firstNode.getNodeInfo().setScriptRuleApplication(true);
            } catch (InterruptedException ie) {
                throw ie;
            } catch (ProofAlreadyClosedException e) {
                if (stateMap.isFailOnClosedOn()) {
                    throw new ScriptException(
                        String.format(
                            "Proof already closed while trying to fetch next goal.\n"
                                            + "This error can be suppressed by setting '@failonclosed off'.\n\n"
                                            + "Command: %s\nPosition: %s\n",
                                    commandContext.getText(),
                                    BuilderHelpers.getPosition(commandContext)),
                            url, commandContext.start.getLine(), commandContext.start.getCharPositionInLine(), e);
                } else {
                    LOGGER.info("Proof already closed at command \"{}\" at line {}, terminating",
                            argMap.get(ScriptLineParser.LITERAL_KEY), BuilderHelpers.getPosition(commandContext));
                    break;
                }
            } catch (Exception e) {
                LOGGER.debug("GOALS: {}", proof.getSubtreeGoals(proof.root()).size());
                proof.getSubtreeGoals(stateMap.getProof().root())
                        .forEach(g -> LOGGER.debug("{}", g.sequent()));
                throw new ScriptException(
                    String.format("Error while executing script: %s%n%nCommand: %s%nPosition: %s%n", e.getMessage(),
                        prettyPrintCommand(commandContext),
                                BuilderHelpers.getPosition(commandContext)),
                    url, commandContext.start.getLine(), commandContext.start.getCharPositionInLine(), e);
            }
        }
    }


    public static String prettyPrintCommand(KeYParser.ProofScriptCommandContext ctx) {
        return (ctx.AT() != null ? "@ " : "") +
                ctx.cmd.getText() +
                (ctx.proofScriptParameters() != null
                        ? " " + ctx.proofScriptParameters().proofScriptParameter().stream()
                        .map(RuleContext::getText)
                        .collect(Collectors.joining(" "))
                        : "") + ";";
    }


    private Map<String, Object> getArguments(KeYParser.ProofScriptCommandContext commandContext) {
        var map = new TreeMap<String, Object>();
        int i = KEY_START_INDEX_PARAMETER;

        if (commandContext.proofScriptParameters() != null) {
            for (var pc : commandContext.proofScriptParameters().proofScriptParameter()) {
                String key = pc.pname != null ? pc.pname.getText() : "#" + (i++);
                map.put(key, pc.expr);
            }
        }
        var in = commandContext.start.getTokenSource().getInputStream();
        var txt = in.getText(Interval.of(commandContext.start.getStartIndex(), commandContext.stop.getStopIndex()));
        map.put(ScriptLineParser.LITERAL_KEY, txt);
        return map;
    }


    public EngineState getStateMap() {
        return stateMap;
    }

    /**
     * Set the routine that is executed before every successfully executed command.
     *
     * @param monitor the monitor to set
     */
    public void setCommandMonitor(Consumer<Message> monitor) {
        this.commandMonitor = monitor;
    }

    public static ProofScriptCommand<?> getCommand(String commandName) {
        return COMMANDS.get(commandName);
    }

    public interface Message {
    }

    public record EchoMessage(String message) implements Message {
    }

    public record ExecuteInfo(String command, Location location, int nodeSerial) implements Message {
    }
}
