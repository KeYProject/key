/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.io.IOException;
import java.net.URI;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.antlr.v4.runtime.RuleContext;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
public class ProofScriptEngine {
    private static final Map<String, ProofScriptCommand> COMMANDS = loadCommands();
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofScriptEngine.class);

    private final List<ScriptCommandAst> script;

    /**
     * The initially selected goal.
     */
    private final @Nullable Goal initiallySelectedGoal;

    /**
     * The engine state map.
     */
    private EngineState stateMap;

    private @Nullable Consumer<Message> commandMonitor;

    public ProofScriptEngine(Path file) throws IOException {
        this(ParsingFacade.parseScript(file), null);
    }

    public ProofScriptEngine(KeyAst.ProofScript script) {
        this(script, null);
    }

    /**
     * Instantiates a new proof script engine.
     *
     * @param script the script
     * @param initiallySelectedGoal the initially selected goal
     */
    public ProofScriptEngine(KeyAst.ProofScript script, Goal initiallySelectedGoal) {
        this(script.asAst(), initiallySelectedGoal);
    }

    public ProofScriptEngine(List<ScriptCommandAst> script, Goal initiallySelectedGoal) {
        this.initiallySelectedGoal = initiallySelectedGoal;
        this.script = script;
    }

    private static Map<String, ProofScriptCommand> loadCommands() {
        Map<String, ProofScriptCommand> result = new HashMap<>();
        var loader = ServiceLoader.load(ProofScriptCommand.class);

        for (ProofScriptCommand cmd : loader) {
            for (var alias : cmd.getAliases()) {
                result.put(alias, cmd);
            }
        }

        return result;
    }

    public void execute(AbstractUserInterfaceControl uiControl, Proof proof)
            throws IOException, InterruptedException, ScriptException {
        stateMap = new EngineState(proof, this);

        if (initiallySelectedGoal != null) {
            stateMap.setGoal(initiallySelectedGoal);
        }

        if (script.isEmpty()) { // no commands given, no work to do
            return;
        }

        // add the filename (if available) to the statemap.
        try {
            URI url = script.getFirst().location().fileUri();
            stateMap.setBaseFileName(Paths.get(url));
        } catch (NullPointerException | InvalidPathException ignored) {
            // weigl: occurs on windows platforms, due to the fact
            // that the URI contains "<unknown>" from ANTLR4 when read by string
            // "<" is illegal on windows
        }

        // add the observer (if installed) to the state map
        if (commandMonitor != null) {
            stateMap.setObserver(commandMonitor);
        }
        execute(uiControl, script);
    }

    public void execute(AbstractUserInterfaceControl uiControl, ScriptBlock block)
            throws ScriptException, InterruptedException {
        execute(uiControl, block.commands());
    }

    public void execute(AbstractUserInterfaceControl uiControl, List<ScriptCommandAst> commands)
            throws InterruptedException, ScriptException {
        if (script.isEmpty()) { // no commands given, no work to do
            return;
        }

        Location start = script.getFirst().location();
        Proof proof = stateMap.getProof();

        int cnt = 0;
        for (ScriptCommandAst ast : commands) {
            if (Thread.interrupted()) {
                throw new InterruptedException();
            }

            String name = ast.commandName();

            String cmd = ast.asCommandLine();

            final Node firstNode = stateMap.getFirstOpenAutomaticGoal().node();
            if (commandMonitor != null && stateMap.isEchoOn()) {
                commandMonitor.accept(new ExecuteInfo(cmd, start, firstNode.serialNr()));
            }

            try {
                ProofScriptCommand command = COMMANDS.get(name);
                if (command == null) {
                    throw new ScriptException("Unknown command " + name + " at " + ast.location());
                }

                if (stateMap.isEchoOn()) {
                    LOGGER.debug("[{}] goal: {}, source line: {}, command: {}", ++cnt,
                        firstNode.serialNr(), ast.location(), cmd);
                }
                command.execute(uiControl, ast, stateMap);
                firstNode.getNodeInfo().setScriptRuleApplication(true);
            } catch (InterruptedException ie) {
                throw ie;
            } catch (ProofAlreadyClosedException e) {
                if (stateMap.isFailOnClosedOn()) {
                    throw new ScriptException(
                        String.format("""
                                        Proof already closed while trying to fetch next goal.
                                This error can be suppressed by setting '@failonclosed off'.

                                Command: %s
                                Position: %s
                                """,
                            ast.asCommandLine(), ast.location()));
                } else {
                    LOGGER.info(
                        "Proof already closed at command \"{}\" at line {}, terminating",
                        ast.commandName(),
                        ast.location());
                    break;
                }
            } catch (Exception e) {
                LOGGER.debug("GOALS: {}", proof.getSubtreeGoals(proof.root()).size());
                proof.getSubtreeGoals(stateMap.getProof().root())
                        .forEach(g -> LOGGER.debug("{}", g.sequent()));


                throw new ScriptException(
                    String.format("Error while executing script: %s%n%nCommand: %s%nPosition: %s%n",
                        e.getMessage(), ast.asCommandLine(), ast.location()),
                    e);
            }
        }
    }


    public static String prettyPrintCommand(KeYParser.ProofScriptCommandContext ctx) {
        return ctx.cmd.getText() +
            (ctx.proofScriptParameters() != null
                    ? " " + ctx.proofScriptParameters().proofScriptParameter().stream()
                            .map(RuleContext::getText)
                            .collect(Collectors.joining(" "))
                    : "")
            + ";";
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

    public static ProofScriptCommand getCommand(String commandName) {
        return COMMANDS.get(commandName);
    }

    public interface Message {
    }

    public record EchoMessage(String message) implements Message {
    }

    public record ExecuteInfo(String command, Location location, int nodeSerial)
            implements Message {
    }
}
