/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.net.URI;
import java.nio.file.Files;
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

/**
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
public class ProofScriptEngine {
    private static final String SYSTEM_COMMAND_PREFIX = "@";
    private static final int MAX_CHARS_PER_COMMAND = 80;
    private static final Map<String, ProofScriptCommand<?>> COMMANDS = loadCommands();
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofScriptEngine.class);


    private final Location initialLocation;
    private final String script;

    /** The initially selected goal. */
    private final Goal initiallySelectedGoal;

    /** The engine state map. */
    private EngineState stateMap;

    private Consumer<Message> commandMonitor;

    public ProofScriptEngine(File file) throws IOException {
        this.initialLocation = new Location(file.toURI(), Position.newOneBased(1, 1));
        this.script = Files.readString(file.toPath());
        this.initiallySelectedGoal = null;
    }

    public ProofScriptEngine(String script, Location initLocation) {
        this(script, initLocation, null);
    }

    /**
     * Instantiates a new proof script engine.
     *
     * @param script the script
     * @param initLocation the initial location
     * @param initiallySelectedGoal the initially selected goal
     */
    public ProofScriptEngine(String script, Location initLocation, Goal initiallySelectedGoal) {
        this.script = script;
        this.initialLocation = initLocation;
        this.initiallySelectedGoal = initiallySelectedGoal;
    }

    private static Map<String, ProofScriptCommand<?>> loadCommands() {
        Map<String, ProofScriptCommand<?>> result = new HashMap<>();
        ServiceLoader<ProofScriptCommand> loader = ServiceLoader.load(ProofScriptCommand.class);

        for (ProofScriptCommand<?> cmd : loader) {
            result.put(cmd.getName(), cmd);
        }

        return result;
    }

    @SuppressWarnings("unchecked")
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof)
            throws IOException, InterruptedException, ScriptException {

        ScriptLineParser mlp = new ScriptLineParser(new StringReader(script), initialLocation);

        stateMap = new EngineState(proof);

        if (initiallySelectedGoal != null) {
            stateMap.setGoal(initiallySelectedGoal);
        }

        // add the filename (if available) to the statemap.
        Optional<URI> uri = initialLocation.getFileURI();
        if (uri.isPresent()) {
            stateMap.setBaseFileName(Paths.get(uri.get()).toFile());
        }

        // add the observer (if installed) to the state map
        if (commandMonitor != null) {
            stateMap.setObserver(commandMonitor);
        }

        int cnt = 0;
        while (true) {
            if (Thread.interrupted()) {
                throw new InterruptedException();
            }

            ScriptLineParser.ParsedCommand parsed = mlp.parseCommand();
            if (parsed == null) {
                // EOF reached
                break;
            }
            final Map<String, String> argMap = parsed.args;
            final Location start = parsed.start;

            String cmd = "'" + argMap.get(ScriptLineParser.LITERAL_KEY) + "'";
            if (cmd.length() > MAX_CHARS_PER_COMMAND) {
                cmd = cmd.substring(0, MAX_CHARS_PER_COMMAND) + " ...'";
            }

            final Node firstNode = stateMap.getFirstOpenAutomaticGoal().node();
            if (commandMonitor != null && stateMap.isEchoOn()
                    && !Optional.ofNullable(argMap.get(ScriptLineParser.COMMAND_KEY)).orElse("")
                            .startsWith(SYSTEM_COMMAND_PREFIX)) {
                commandMonitor
                        .accept(new ExecuteInfo(cmd, start, firstNode.serialNr()));
            }

            try {
                String name = argMap.get(ScriptLineParser.COMMAND_KEY);
                if (name == null) {
                    throw new ScriptException("No command");
                }

                ProofScriptCommand<Object> command =
                    (ProofScriptCommand<Object>) COMMANDS.get(name);
                if (command == null) {
                    throw new ScriptException("Unknown command " + name);
                }

                Object o = command.evaluateArguments(stateMap, argMap);
                if (!name.startsWith(SYSTEM_COMMAND_PREFIX) && stateMap.isEchoOn()) {
                    LOGGER.debug("[{}] goal: {}, source line: {}, command: {}", ++cnt,
                        firstNode.serialNr(), parsed.start.getPosition().line(), cmd);
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
                                + "Command: %s\nLine:%d\n",
                            argMap.get(ScriptLineParser.LITERAL_KEY), start.getPosition().line()),
                        start, e);
                } else {
                    LOGGER.info(
                        "Proof already closed at command \"{}\" at line %d, terminating in line {}",
                        argMap.get(ScriptLineParser.LITERAL_KEY), start.getPosition().line());
                    break;
                }
            } catch (Exception e) {
                LOGGER.debug("GOALS: {}", proof.getSubtreeGoals(proof.root()).size());
                proof.getSubtreeGoals(stateMap.getProof().root())
                        .forEach(g -> LOGGER.debug("{}", g.sequent()));
                throw new ScriptException(
                    String.format("Error while executing script: %s\n\nCommand: %s", e.getMessage(),
                        argMap.get(ScriptLineParser.LITERAL_KEY)),
                    start, e);
            }
        }
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

    public static final class EchoMessage implements Message {
        public final String message;

        public EchoMessage(String message) {
            this.message = message;
        }
    }

    public static final class ExecuteInfo implements Message {
        public final String command;
        public final Location location;
        public final int nodeSerial;

        public ExecuteInfo(String command, Location location, int nodeSerial) {
            this.command = command;
            this.location = location;
            this.nodeSerial = nodeSerial;
        }
    }
}
