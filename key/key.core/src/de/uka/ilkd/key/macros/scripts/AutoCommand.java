package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.Profile;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.Map;

/**
 * The AutoCommand invokes the automatic strategy "Auto"
 * It has no parameters
 *
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
public class AutoCommand extends AbstractCommand<AutoCommand.Parameters> {

    public AutoCommand() {
        super(Parameters.class);
    }

    @Override public String getName() {
        return "auto";
    }

    @Override public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) {
        Parameters args = new Parameters();
        try {
            ValueInjector.getInstance().inject(this, args, arguments);
        }
        catch (Exception e) {
            e.printStackTrace();
        }
        return args;
    }

    @Override public void execute(AbstractUserInterfaceControl uiControl,
            Parameters arguments, EngineState state)
            throws ScriptException, InterruptedException {

        Profile profile = state.getProof().getServices().getProfile();

        //
        // create the rule application engine
        final ApplyStrategy applyStrategy = new ApplyStrategy(
                profile.getSelectedGoalChooserBuilder().create());

        //
        // find the targets
        ImmutableList<Goal> goals;
        if (arguments.isOnAllOpenGoals()) {
            goals = state.getProof().openGoals();
        }
        else {
            goals = ImmutableSLList.<Goal>nil()
                    .prepend(state.getFirstOpenGoal());
        }

        //
        // set the max number of steps if given
        int oldNumberOfSteps = state.getMaxAutomaticSteps();
        if (arguments.getSteps() > 0)
            state.setMaxAutomaticSteps(arguments.getSteps());

        //
        // Give some feedback
        applyStrategy.addProverTaskObserver(uiControl);
        // TODO get rid of that cast.

        //
        // start actual autoprove
        try {
            for (Goal goal : goals) {
                applyStrategy.start(state.getProof(),
                        ImmutableSLList.<Goal>nil().prepend(goal));

                // only now reraise the interruption exception
                if (applyStrategy.hasBeenInterrupted()) {
                    throw new InterruptedException();
                }

            }
        }
        finally {
            state.setMaxAutomaticSteps(oldNumberOfSteps);
        }
    }

    static class Parameters {
        @Option(value = "all", required = false) public boolean onAllOpenGoals = false;

        @Option(value = "steps", required = false) public int maxSteps = -1;

        public boolean isOnAllOpenGoals() {
            return onAllOpenGoals;
        }

        public void setOnAllOpenGoals(boolean onAllOpenGoals) {
            this.onAllOpenGoals = onAllOpenGoals;
        }

        public int getSteps() {
            return maxSteps;
        }

    }
}
