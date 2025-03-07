/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.scripts.meta.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.strategy.AutomatedRuleApplicationManager;
import de.uka.ilkd.key.strategy.FocussedBreakpointRuleApplicationManager;

import de.uka.ilkd.key.strategy.StrategyProperties;
import org.jspecify.annotations.NullMarked;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * The AutoCommand invokes the automatic strategy "Auto".
 *
 * See documentation of {@link Parameters} for more information.
 *
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
@NullMarked
public class AutoCommand extends AbstractCommand<AutoCommand.Parameters> {

    public AutoCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "auto";
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, Object> arguments)
            throws ConversionException, ArgumentRequiredException, InjectionReflectionException,
            NoSpecifiedConverterException {
        Parameters args = new Parameters();
        state.getValueInjector().inject(this, args, arguments);
        args.originalArgs = arguments;
        return args;
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters arguments,
            EngineState state) throws ScriptException, InterruptedException {
        final Services services = state.getProof().getServices();
        final Profile profile = services.getProfile();

        // create the rule application engine
        final ProverCore applyStrategy =
            new ApplyStrategy(profile.getSelectedGoalChooserBuilder().create());

        // find the targets
        final ImmutableList<Goal> goals;
        if (arguments.onAllOpenGoals) {
            goals = state.getProof().openGoals();
        } else {
            final Goal goal = state.getFirstOpenAutomaticGoal();
            goals = ImmutableSLList.<Goal>nil().prepend(goal);

            final Optional<String> matchesRegEx = Optional.ofNullable(arguments.matches);
            final Optional<String> breakpoint = Optional.ofNullable(arguments.breakpoint);
            if (matchesRegEx.isPresent() || breakpoint.isPresent()) {
                setupFocussedBreakpointStrategy( //
                    matchesRegEx, breakpoint, goal, applyStrategy, services);
            }
        }

        // set the max number of steps if given
        int oldNumberOfSteps = state.getMaxAutomaticSteps();
        if (arguments.getSteps() > 0) {
            state.setMaxAutomaticSteps(arguments.getSteps());
        }

        // set model search if given
        StrategyProperties activeStrategyProperties =
            state.getProof().getSettings().getStrategySettings().getActiveStrategyProperties();

        Map<String, OriginalValue> orgValues = prepareOriginalValues();
        for (Entry<String, Object> entry : arguments.originalArgs.entrySet()) {
            OriginalValue ov = orgValues.get(entry.getKey());
            if(ov != null) {
                ov.oldValue = activeStrategyProperties.getProperty(ov.settingName);
                activeStrategyProperties.setProperty(ov.settingName,
                        "true".equals(entry.getValue()) ? ov.trueValue : ov.falseValue);
            }
        }

        SetCommand.updateStrategySettings(state, activeStrategyProperties);

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
            for (OriginalValue ov : orgValues.values()) {
                if (ov.oldValue != null) {
                    activeStrategyProperties.setProperty(ov.settingName, ov.oldValue);
                }
            }
            SetCommand.updateStrategySettings(state, activeStrategyProperties);
        }
    }

    private Map<String, OriginalValue> prepareOriginalValues() {
        var res = new HashMap<String, OriginalValue>();
        res.put("modelSearch", new OriginalValue(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_COMPLETION, StrategyProperties.NON_LIN_ARITH_DEF_OPS));
        res.put("expandQueries", new OriginalValue(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_ON, StrategyProperties.QUERYAXIOM_OFF));
        res.put("classAxioms", new OriginalValue(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, StrategyProperties.CLASS_AXIOM_FREE, StrategyProperties.CLASS_AXIOM_OFF));
        res.put("dependencies", new OriginalValue(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_ON, StrategyProperties.DEP_OFF));
        // ... add further (boolean for the moment) setings here.
        return res;
    }

    /**
     * Sets up a focused automatic strategy. Focus is on the sequent formula matching the
     * matchesRegEx (may not be null).
     *
     * @param maybeMatchesRegEx The RegEx which should match on the sequent formula to focus.
     * @param breakpointArg An optional breakpoint argument.
     * @param goal The {@link Goal} to apply the strategy on, needed for the rule
     *        application* manager.
     * @param proverCore The {@link ProverCore}, needed for resetting the strategy
     *        afterward.
     * @param services The {@link Services} object.
     * @throws ScriptException
     */
    private void setupFocussedBreakpointStrategy(final Optional<String> maybeMatchesRegEx,
            final Optional<String> breakpointArg, final Goal goal, final ProverCore proverCore,
            final Services services) throws ScriptException {
        final Optional<PosInOccurrence> focus = maybeMatchesRegEx.isPresent()
                ? Optional.of(MacroCommand.extractMatchingPio(goal.node().sequent(),
                    maybeMatchesRegEx.get(), services))
                : Optional.empty();

        final AutomatedRuleApplicationManager realManager = //
            goal.getRuleAppManager();
        goal.setRuleAppManager(null);

        final AutomatedRuleApplicationManager focusManager = //
            new FocussedBreakpointRuleApplicationManager(realManager, goal, focus, breakpointArg);
        goal.setRuleAppManager(focusManager);

        proverCore.addProverTaskObserver(
            new AbstractProofControl.FocussedAutoModeTaskListener(services.getProof()));
    }

    @Documentation("""
                    The AutoCommand is a command that invokes the automatic strategy "Auto" of KeY.
                    It can be used to automatically prove a goal or a set of goals.
                    Use with care, as this command may leave the proof state in an unpredictable state
                    with many open goals.
                    
                    Use the command with "close" to make sure the command succeeds for fails without
                    changes.""")
    public static class Parameters {
        //@ TODO Deprecated with the higher order proof commands?
        @Option(value = "all", required = false, help = "Apply the strategy on all open goals. There is a better syntax for that now.")
        public boolean onAllOpenGoals = false;

        @Option(value = "steps", required = false, help = "The maximum number of steps to be performed.")
        public int maxSteps = -1;

        /**
         * Run on formula matching the given regex
         */
        @Option(value = "matches", required = false, help = "Run on formula matching the given regex.")
        public String matches = null;

        /**
         * Run on formula matching the given regex
         */
        @Option(value = "breakpoint", required = false, help = "Run on formula matching the given regex.")
        public String breakpoint = null;

        @Option(value = "modelsearch", required = false, help = "Enable model search. Better for some types of arithmetic problems. Sometimes a lot worse")
        public Boolean modelSearch;

        @Option(value = "expandQueries", required = false, help = "Expand queries by modalities.")
        public Boolean expandQueries;

        @Option(value = "classAxioms", required = false, help = "Enable class axioms. This expands model methods and fields and invariants quite eagerly. May lead to divergence.")
        public Boolean classAxioms;

        @Option(value = "dependencies", required = false, help = "Enable dependency reasoning. In modular reasoning, the value of symbols may stay the same, without that its definition is known. May be an enabler, may be a showstopper.")
        public Boolean dependencies;

        public int getSteps() {
            return maxSteps;
        }

        public Map<String, Object> originalArgs;
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
