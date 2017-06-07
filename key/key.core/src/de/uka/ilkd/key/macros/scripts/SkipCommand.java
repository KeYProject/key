package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;

public class SkipCommand extends NoArgumentCommand {
    @Override public void execute(AbstractUserInterfaceControl uiControl,
            Void args, EngineState stateMap)
            throws ScriptException, InterruptedException {

    }

    @Override public String getName() {
        return "skip";
    }

}
