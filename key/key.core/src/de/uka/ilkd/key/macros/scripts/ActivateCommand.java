package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;

public class ActivateCommand extends NoArgumentCommand {
    @Override
    public String getName() {
        return "activate";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Void args,
            EngineState state) throws ScriptException, InterruptedException {
        Goal goal = state.getFirstOpenGoal(false);
        goal.setEnabled(true);
    }

}
