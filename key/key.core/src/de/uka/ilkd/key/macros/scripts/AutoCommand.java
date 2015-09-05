package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.init.Profile;

public class AutoCommand extends AbstractCommand {

    @Override
    public String getName() {
        return "auto";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args) throws ScriptException, InterruptedException {

        Profile profile = proof.getServices().getProfile();

        //
        // create the rule application engine
        final ApplyStrategy applyStrategy =
                new ApplyStrategy(profile.getSelectedGoalChooserBuilder().create());

        //
        // find the targets
        ImmutableList<Goal> goals;
        if(args.containsKey("all")) {
            goals = proof.openGoals();
        } else {
            goals = ImmutableSLList.<Goal>nil().prepend(getFirstOpenGoal(proof));
        }

        //
        // set the max number of steps if given
        int oldNumberOfSteps = getMaxAutomaticSteps(proof);
        if(args.containsKey("steps")) {
            try {
                int numberSteps = Integer.parseInt(args.get("steps"));
                setMaxAutomaticSteps(proof, numberSteps);
            } catch(NumberFormatException nfe) {
                throw new ScriptException("steps expects an integer", nfe);
            }
        }

        //
        // Give some feedback
        applyStrategy.addProverTaskObserver((ProverTaskListener)uiControl);
        // TODO get rid of that cast.

        //
        // start actual autoprove
        try {
            for (Goal goal : goals) {
                applyStrategy.start(proof, ImmutableSLList.<Goal>nil().prepend(goal));

                // only now reraise the interruption exception
                if(applyStrategy.hasBeenInterrupted()) {
                    throw new InterruptedException();
                }

            }
        } finally {
            setMaxAutomaticSteps(proof, oldNumberOfSteps);
        }
    }

}
