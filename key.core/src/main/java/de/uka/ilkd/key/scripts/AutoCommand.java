/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.scripts.meta.Option;
import de.uka.ilkd.key.scripts.meta.Option;
import de.uka.ilkd.key.strategy.FocussedBreakpointRuleApplicationManager;

import org.key_project.prover.engine.ProverCore;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.RuleApplicationManager;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.Nullable;

/**
 * The AutoCommand invokes the automatic strategy "Auto".
 *
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
public class AutoCommand extends AbstractCommand {

    public AutoCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "auto";
    }

    @Override
    public String getDocumentation() {
        return "The AutoCommand invokes the automatic strategy \"Auto\"";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, ScriptCommandAst args,
            EngineState state) throws ScriptException, InterruptedException {
        var arguments = state.getValueInjector().inject(this, new AutoCommand.Parameters(), args);
        final Services services = state.getProof().getServices();
        final Profile profile = services.getProfile();

        // create the rule application engine
        final ProverCore<Proof, Goal> applyStrategy =
            new ApplyStrategy(profile.<Proof, Goal>getSelectedGoalChooserBuilder().create());

        // find the targets
        final ImmutableList<Goal> goals;
        if (arguments.isOnAllOpenGoals()) {
            goals = state.getProof().openGoals();
        } else {
            final Goal goal = state.getFirstOpenAutomaticGoal();
            goals = ImmutableSLList.<Goal>nil().prepend(goal);

            if (arguments.matches != null || arguments.breakpoint != null) {
                setupFocussedBreakpointStrategy( //
                    arguments.matches, arguments.breakpoint, goal, applyStrategy, services);
            }
        }

        // set the max number of steps if given
        int oldNumberOfSteps = state.getMaxAutomaticSteps();
        if (arguments.getSteps() > 0) {
            state.setMaxAutomaticSteps(arguments.getSteps());
        }

        // Give some feedback
        applyStrategy.addProverTaskObserver(uiControl);

        // start actual autoprove
        try {
            for (Goal goal : goals) {
                applyStrategy.start(state.getProof(), ImmutableSLList.<Goal>nil().prepend(goal));

                // only now reraise the interruption exception
                if (applyStrategy.hasBeenInterrupted()) {
                    throw new InterruptedException();
                }

            }
        } finally {
            state.setMaxAutomaticSteps(oldNumberOfSteps);
        }
    }

    /**
     * Sets up a focused automatic strategy. Focus is on the sequent formula matching the
     * matchesRegEx (may not be null).
     *
     * @param maybeMatchesRegEx The RegEx which should match on the sequent formula to focus.
     * @param breakpointArg An optional breakpoint argument.
     * @param goal The {@link Goal} to apply the strategy on, needed for the rule* application
     *        manager.
     * @param proverCore The {@link ProverCore}, needed for resetting the strategy* afterward.
     * @param services The {@link Services} object.
     * @throws ScriptException
     */
    private void setupFocussedBreakpointStrategy(final String maybeMatchesRegEx,
            final String breakpointArg, final Goal goal, final ProverCore proverCore,
            final Services services) throws ScriptException {
        final PosInOccurrence focus =
            MacroCommand.extractMatchingPio(goal.node().sequent(), maybeMatchesRegEx, services);

        final RuleApplicationManager realManager = //
            goal.getRuleAppManager();
        goal.setRuleAppManager(null);

        final RuleApplicationManager focusManager = //
            new FocussedBreakpointRuleApplicationManager(realManager, goal, focus, breakpointArg);
        goal.setRuleAppManager(focusManager);

        proverCore.addProverTaskObserver(
            new AbstractProofControl.FocussedAutoModeTaskListener(services.getProof()));
    }

    public static class Parameters {
        @Option(value = "all", required = false)
        public boolean onAllOpenGoals = false;

        @Option(value = "steps", required = false)
        public int maxSteps = -1;

        /**
         * Run on formula matching the given regex
         */
        @Option(value = "matches", required = false)
        public @Nullable String matches = null;

        /**
         * Run on formula matching the given regex
         */
        @Option(value = "breakpoint", required = false)
        public @Nullable String breakpoint = null;

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
