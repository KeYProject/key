package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.nio.file.NoSuchFileException;
import java.util.Map;
import java.util.Observer;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;

public class ScriptCommand extends AbstractCommand {

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> stateMap)
            throws ScriptException, InterruptedException {

        String filename = args.get("#2");
        File file;
        Object baseFileObject = stateMap.get(ProofScriptEngine.BASE_FILE_NAME_KEY);
        if(baseFileObject != null) {
            File baseFile = new File(baseFileObject.toString());
            file = new File(baseFile.getParent(), filename);
        } else {
            file = new File(filename);
        }

        System.err.println("Included script " + file);

        try {
            ProofScriptEngine pse = new ProofScriptEngine(file);
            pse.setCommandMonitor((Observer) stateMap.get(ProofScriptEngine.OBSERVER_KEY));
            pse.execute(uiControl, proof);
        } catch(NoSuchFileException e) {
            // The message is very cryptic otherwise.
            throw new ScriptException("Script file '" + filename + "' not found", e);
        } catch (Exception e) {
            throw new ScriptException("Error while running script'" + filename
                    + "': " + e.getMessage(), e);
        }
    }

    @Override
    public String getName() {
        return "script";
    }

}
