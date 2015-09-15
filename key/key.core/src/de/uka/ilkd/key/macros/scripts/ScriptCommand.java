package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;

public class ScriptCommand extends AbstractCommand {

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> stateMap)
            throws ScriptException, InterruptedException {

        String filename = args.get("#2");

        try {
            ProofScriptEngine pse = new ProofScriptEngine(new File(filename));
            pse.execute(uiControl, proof);
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
