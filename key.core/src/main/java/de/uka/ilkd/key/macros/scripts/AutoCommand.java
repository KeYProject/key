/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.macros.scripts;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;


import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.AutomatedRuleApplicationManager;
import de.uka.ilkd.key.strategy.FocussedBreakpointRuleApplicationManager;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * The AutoCommand invokes the automatic strategy "Auto".
 *
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
public class AutoCommand extends AbstractCommand<AutoCommand.Parameters> {

    public AutoCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "auto";
    }

    @Override
    public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) {
        Parameters args = new Parameters();
        try {
            ValueInjector.getInstance().inject(this, args, arguments);
        } catch (Exception e) {
            e.printStackTrace();
        }
        args.originalArgs = arguments;
        return args;
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl,
            Parameters arguments, EngineState state)
            throws ScriptException, InterruptedException {
        final Services services = state.getProof().getServices();
        final Profile profile = services.getProfile();

        // create the rule application engine
        final ProverCore applyStrategy = new ApplyStrategy(
            profile.getSelectedGoalChooserBuilder().create());

        // find the targets
        final ImmutableList<Goal> goals;
        if (arguments.onAllOpenGoals) {
            goals = state.getProof().openGoals();
        } else {
            final Goal goal = state.getFirstOpenAutomaticGoal();
            goals = ImmutableSLList.<Goal>nil().prepend(goal);

            final Optional<String> matchesRegEx = Optional
                    .ofNullable(arguments.matches);
            final Optional<String> breakpoint = Optional
                    .ofNullable(arguments.breakpoint);
            if (matchesRegEx.isPresent() || breakpoint.isPresent()) {
                setupFocussedBreakpointStrategy( //
                    matchesRegEx, breakpoint, goal, applyStrategy,
                    services);
            }
        }

        // set the max number of steps if given
        int oldNumberOfSteps = state.getMaxAutomaticSteps();
        if (arguments.getSteps() > 0)
            state.setMaxAutomaticSteps(arguments.getSteps());

        // set model search if given
        StrategyProperties activeStrategyProperties =
            state.getProof().getSettings().getStrategySettings().getActiveStrategyProperties();

        Map<String, OriginalValue> orgValues = prepareOriginalValues();
        for (Entry<String, String> entry : arguments.originalArgs.entrySet()) {
            OriginalValue ov = orgValues.get(entry.getKey());
            if(ov != null) {
                ov.oldValue = activeStrategyProperties.getProperty(ov.settingName);
                activeStrategyProperties.setProperty(ov.settingName,
                        "true".equals(entry.getValue()) ? ov.trueValue : ov.falseValue);
            }
        }

        SetCommand.updateStrategySettings(state, activeStrategyProperties);

        final Strategy originalStrategy = state.getProof().getActiveStrategy();
        if (arguments.additionalRules != null) {
            state.getProof().setActiveStrategy(new AdditionalRulesStrategy(originalStrategy, arguments.additionalRules));
        }

        // Give some feedback
        applyStrategy.addProverTaskObserver(uiControl);

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
        } finally {
            state.setMaxAutomaticSteps(oldNumberOfSteps);
            for (OriginalValue ov : orgValues.values()) {
                if (ov.oldValue != null) {
                    activeStrategyProperties.setProperty(ov.settingName, ov.oldValue);
                }
            }
            state.getProof().setActiveStrategy(originalStrategy);
            SetCommand.updateStrategySettings(state, activeStrategyProperties);
        }
    }

    private Map<String, OriginalValue> prepareOriginalValues() {
        var res = new HashMap<String, OriginalValue>();
        res.put("modelSearch", new OriginalValue(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_COMPLETION, StrategyProperties.NON_LIN_ARITH_DEF_OPS));
        res.put("expandQueries", new OriginalValue(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_ON, StrategyProperties.QUERYAXIOM_OFF));
        res.put("classAxioms", new OriginalValue(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, StrategyProperties.CLASS_AXIOM_FREE, StrategyProperties.CLASS_AXIOM_OFF));
        res.put("dependencies", new OriginalValue(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_ON, StrategyProperties.DEP_OFF));
        res.put("proofSplitting", new OriginalValue(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_NORMAL, StrategyProperties.SPLITTING_OFF));
        return res;
    }

    /**
     * Sets up a focused automatic strategy. Focus is on the sequent formula
     * matching the matchesRegEx (may not be null).
     *
     * @param maybeMatchesRegEx
     *        The RegEx which should match on the sequent formula to focus.
     * @param breakpointArg
     *        An optional breakpoint argument.
     * @param goal
     *        The {@link Goal} to apply the strategy on, needed for the rule
     *        application manager.
     * @param proverCore
     *        The {@link ProverCore}, needed for resetting the strategy
     *        afterward.
     * @param services
     *        The {@link Services} object.
     * @throws ScriptException
     */
    private void setupFocussedBreakpointStrategy(
            final Optional<String> maybeMatchesRegEx,
            final Optional<String> breakpointArg, final Goal goal,
            final ProverCore proverCore, final Services services)
            throws ScriptException {
        final Optional<PosInOccurrence> focus = maybeMatchesRegEx.isPresent()
                ? Optional.of(
                    MacroCommand.extractMatchingPio(goal.node().sequent(),
                        maybeMatchesRegEx.get(), services))
                : Optional.empty();

        final AutomatedRuleApplicationManager realManager = //
            goal.getRuleAppManager();
        goal.setRuleAppManager(null);

        final AutomatedRuleApplicationManager focusManager = //
            new FocussedBreakpointRuleApplicationManager(realManager, goal,
                focus, breakpointArg);
        goal.setRuleAppManager(focusManager);

        proverCore.addProverTaskObserver(
            new AbstractProofControl.FocussedAutoModeTaskListener(
                services.getProof()));
    }

    public static class Parameters {
        @Option(value = "all", required = false)
        public boolean onAllOpenGoals = false;

        @Option(value = "steps", required = false)
        public int maxSteps = -1;

        /** Run on formula matching the given regex */
        @Option(value = "matches", required = false)
        public String matches = null;

        /** Run on formula matching the given regex */
        @Option(value = "breakpoint", required = false)
        public String breakpoint = null;

        @Option(value = "modelsearch", required = false)
        public Boolean modelSearch;

        @Option(value = "expandQueries", required = false)
        public Boolean expandQueries;

        @Option(value = "classAxioms", required = false)
        public Boolean classAxioms;

        @Option(value = "dependencies", required = false)
        public Boolean dependencies;

        @Option(value = "proofSplitting", required = false)
        public Boolean proofSplitting;

        @Varargs(prefix = "add_")
        public Map<String, String> additionalRules;

        public int getSteps() {
            return maxSteps;
        }

        public Map<String, String> originalArgs;

    }

    private static final class OriginalValue {
        private final String settingName;
        private final String trueValue;
        private final String falseValue;
        private String oldValue;

        private OriginalValue( String settingName, String trueValue, String falseValue) {
            this.settingName = settingName;
            this.trueValue = trueValue;
            this.falseValue = falseValue;
        }

        @Override
        public String toString() {
            return "OriginalValue{" +
                    "settingName='" + settingName + '\'' +
                    ", trueValue='" + trueValue + '\'' +
                    ", falseValue='" + falseValue + '\'' +
                    ", oldValue='" + oldValue + '\'' +
                    '}';
        }
    }
}
