package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;
import java.util.Observer;
import java.util.Optional;
import java.util.ServiceLoader;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
public class ProofScriptEngine {
    private static final String SYSTEM_COMMAND_PREFIX = "@";
    private static final int MAX_CHARS_PER_COMMAND = 80;
    private static final Map<String, ProofScriptCommand> COMMANDS = loadCommands();

    private final Location initialLocation;
    private final String script;

    /** The initially selected goal. */
    private final Goal initiallySelectedGoal;

    /** The engine state map. */
    private EngineState stateMap;

    private Observer commandMonitor;

    public ProofScriptEngine(File file) throws IOException {
        this.initialLocation = new Location(file.toURI().toURL(), 1, 1);
        this.script = new String(Files.readAllBytes(file.toPath()));
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

    private static Map<String, ProofScriptCommand> loadCommands() {
        Map<String, ProofScriptCommand> result = new HashMap<String, ProofScriptCommand>();
        ServiceLoader<ProofScriptCommand> loader = ServiceLoader
                .load(ProofScriptCommand.class);

        for (ProofScriptCommand<?> cmd : loader) {
            result.put(cmd.getName(), cmd);
        }

        return result;
    }

    @SuppressWarnings("unchecked")
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof)
            throws IOException, InterruptedException, ScriptException {

        ScriptLineParser mlp = new ScriptLineParser(new StringReader(script));
        mlp.setLocation(initialLocation);

        stateMap = new EngineState(proof);

        if (initiallySelectedGoal != null) {
            stateMap.setGoal(initiallySelectedGoal);
        }

        // add the filename (if available) to the statemap.
        URL url = initialLocation.getFileURL();
        if (url != null) {
            try {
                stateMap.setBaseFileName(Paths.get(url.toURI()).toFile());
            } catch (URISyntaxException e) {
                throw new IOException(e);
            }
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

            Map<String, String> argMap = mlp.parseCommand();
            if (argMap == null) {
                // EOF reached
                break;
            }

            String cmd = "'" + argMap.get(ScriptLineParser.LITERAL_KEY) + "'";
            if (cmd.length() > MAX_CHARS_PER_COMMAND) {
                cmd = cmd.substring(0, MAX_CHARS_PER_COMMAND) + " ...'";
            }

            if (commandMonitor != null && stateMap.isEchoOn() && !Optional
                    .ofNullable(argMap.get(ScriptLineParser.COMMAND_KEY))
                    .orElse("").startsWith(SYSTEM_COMMAND_PREFIX)) {
                commandMonitor.update(null, cmd);
            }

            try {
                String name = argMap.get(ScriptLineParser.COMMAND_KEY);
                if (name == null) {
                    throw new ScriptException("No command");
                }

                ProofScriptCommand<Object> command = COMMANDS.get(name);
                if (command == null) {
                    throw new ScriptException("Unknown command " + name);
                }

                if (!name.startsWith(SYSTEM_COMMAND_PREFIX)
                        && stateMap.isEchoOn()) {
                    System.out.format("%5d: %s%n", ++cnt, cmd);
                }
                // write("/tmp/weiglProofScripts_%d.txt", cnt, proof);

                Object o = command.evaluateArguments(stateMap, argMap);
                final Node firstNode = stateMap.getFirstOpenAutomaticGoal().node();
                command.execute(uiControl, o, stateMap);
                firstNode.getNodeInfo().setScriptRuleApplication(true);
            } catch (InterruptedException ie) {
                throw ie;
            } catch (Exception e) {
                //@formatter:off
                //System.out.println("GOALS:" + proof.getSubtreeGoals(proof.root()).size());
                //proof.getSubtreeGoals(stateMap.getProof().root()).forEach(g -> {
                //            System.out.println("====");
                //            System.out.println(g.sequent());
                //            System.out.println("====");
                //        }
                //);
                //@formatter:on

                throw new ScriptException(
                        "Error while executing script: " + e.getMessage()
                                + "\n\nCommand: "
                                + argMap.get(ScriptLineParser.LITERAL_KEY),
                        initialLocation.getFileURL(), mlp.getLine(),
                        mlp.getColumn(), e);
            }
        }
    }

    public EngineState getStateMap() {
        return stateMap;
    }

//    private void write(String s, int cnt, Proof proof) {
//        try (FileWriter fw = new FileWriter(String.format(s, cnt))) {
//            fw.write(proof.toString());
//        } catch (IOException e) {
//            System.err.println(e.getMessage());
//        }
//    }

    /**
     * Set the routine that is executed before every successfully executed
     * command.
     *
     * @param monitor
     *            the monitor to set
     */
    public void setCommandMonitor(Observer monitor) {
        this.commandMonitor = monitor;
    }
}
