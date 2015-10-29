package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

public class LeaveCommand extends AbstractCommand {

    @Override
    public String getName() {
        return "leave";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> state) throws ScriptException, InterruptedException {
        Goal goal = getFirstOpenGoal(proof, state);
        System.err.println("Deactivating " + goal.node().serialNr());
        goal.setEnabled(false);
    }

}
