package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;

public class TryCloseCommand extends AbstractCommand {

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> state) throws ScriptException, InterruptedException {

        String stepsStr = args.get("steps");
        TryCloseMacro macro;
        if(stepsStr != null) {
            try {
                int steps = Integer.parseInt(stepsStr);
                macro = new TryCloseMacro(steps);
            } catch (NumberFormatException e) {
                throw new ScriptException("Not a number: " + stepsStr, e);
            }
        } else {
            macro = new TryCloseMacro();
        }

        boolean branch = "branch".equals(args.get("#2"));

        Node target;
        if(branch) {
            target = getFirstOpenGoal(proof, state).node();
        } else {
            target = proof.root();
        }

        try {
            macro.applyTo(uiControl, target, null, (ProverTaskListener)uiControl);
        } catch (Exception e) {
            throw new ScriptException("tryclose caused an exception: " + e.getMessage(), e);
        }
    }

    @Override
    public String getName() {
        return "tryclose";
    }

}
