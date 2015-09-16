package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;

public class ExitCommand extends AbstractCommand {

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> state) throws ScriptException,
            InterruptedException {
        throw new InterruptedException("Interruption requested from within script");
    }

    @Override
    public String getName() {
        return "exit";
    }

}
