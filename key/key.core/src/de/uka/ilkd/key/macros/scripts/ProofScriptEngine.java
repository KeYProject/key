package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.Map;
import java.util.Observer;
import java.util.ServiceLoader;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Proof;

public class ProofScriptEngine {

    private static final int MAX_CHARS_PER_COMMAND = 80;

    public static final String BASE_FILE_NAME_KEY = "baseFileName";

    private static final Map<String, ProofScriptCommand> COMMANDS = loadCommands();

    private final Location initialLocation;
    private final String script;

    private Observer commandMonitor;

    public ProofScriptEngine(File file) throws IOException {
        this.initialLocation = new Location(file.getAbsolutePath(), 1, 1);
        this.script = new String(Files.readAllBytes(file.toPath()));
    }

    public ProofScriptEngine(String script, Location initLocation) {
        this.script = script;
        this.initialLocation = initLocation;
    }

    private static Map<String, ProofScriptCommand> loadCommands() {
        Map<String, ProofScriptCommand> result = new HashMap<String, ProofScriptCommand>();
        ServiceLoader<ProofScriptCommand> loader = ServiceLoader.load(ProofScriptCommand.class);

        for (ProofScriptCommand cmd : loader) {
            result.put(cmd.getName(), cmd);
        }

        return result;
    }

    public void execute(AbstractUserInterfaceControl uiControl, Proof proof)
            throws IOException, InterruptedException, ScriptException {

        ScriptLineParser mlp = new ScriptLineParser(new StringReader(script));
        mlp.setLocation(initialLocation.getLine(), initialLocation.getColumn());

        Map<String, Object> stateMap = new HashMap<String, Object>();

        // add the filename (if available) to the statemap.
        String filename = initialLocation.getFilename();
        if(filename != null && filename.length() > 0) {
            stateMap.put(BASE_FILE_NAME_KEY, filename);
        }

        while(true) {

            if(Thread.interrupted()) {
                throw new InterruptedException();
            }

            Map<String, String> argMap = mlp.parseCommand();
            if(argMap == null) {
                // EOF reached
                break;
            }

            String cmd = "'" + argMap.get(ScriptLineParser.LITERAL_KEY) + "'";
            if(cmd.length() > MAX_CHARS_PER_COMMAND) {
                cmd = cmd.substring(0, MAX_CHARS_PER_COMMAND) + " ...'";
            }

            if(commandMonitor != null) {
                commandMonitor.update(null, cmd);
            }
            System.out.println("Command: " + cmd);

            try {
                String name = argMap.get(ScriptLineParser.COMMAND_KEY);
                if(name == null) {
                    throw new ScriptException("No command");
                }

                ProofScriptCommand command = COMMANDS.get(name);
                if(command == null) {
                    throw new ScriptException("Unknown command " + name);
                }

                command.execute(uiControl, proof, argMap, stateMap);
            } catch(InterruptedException ie) {
                throw ie;
            } catch (Exception e) {
                throw new ScriptException("Error while executing script: " + e.getMessage() +
                        "\n\nCommand:" + argMap.get(ScriptLineParser.LITERAL_KEY),
                        initialLocation.getFilename(), mlp.getLine(), mlp.getColumn(), e);
            }
        }
    }

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


