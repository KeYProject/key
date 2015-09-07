package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.HashMap;
import java.util.Map;
import java.util.Observer;
import java.util.ServiceLoader;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;

public class ProofScriptEngine {

    private static final Map<String, ProofScriptCommand> COMMANDS = loadCommands();

    private final File file;

    private Observer commandMonitor;

    public ProofScriptEngine(File file) {
        this.file = file;
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

        ScriptLineParser mlp = new ScriptLineParser(file.getAbsolutePath());

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
            if(cmd.length() > 40) {
                cmd = cmd.substring(0,40) + " ...'";
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

                command.execute(uiControl, proof, argMap);
            } catch(InterruptedException ie) {
                throw ie;
            } catch (Exception e) {
                throw new ScriptException("Error while executing script: " + e.getMessage() +
                        "\n\nCommand:" + argMap.get(ScriptLineParser.LITERAL_KEY),
                        file.getAbsolutePath(), mlp.getLine(), mlp.getColumn(), e);
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


