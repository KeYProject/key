package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.macros.scripts.meta.Description;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.strategy.AutomatedRuleApplicationManager;
import de.uka.ilkd.key.strategy.FocussedBreakpointRuleApplicationManager;
import de.uka.ilkd.key.strategy.StrategyProperties;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.Map;
import java.util.Optional;

public class OneStepSimplifierCommand extends AbstractCommand<OneStepSimplifierCommand.Parameters> {

    public OneStepSimplifierCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "oss";
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        Parameters args = new Parameters();
        ValueInjector.getInstance().inject(this, args, arguments);
        return args;
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters arguments,
            EngineState state) throws ScriptException, InterruptedException {

        final Goal goal = state.getFirstOpenAutomaticGoal();
        if(arguments.antecedent) {
            for (SequentFormula sf : goal.sequent().antecedent()) {
                ImmutableList<IBuiltInRuleApp> builtins = goal.ruleAppIndex().getBuiltInRules(goal, new PosInOccurrence(sf, PosInTerm.getTopLevel(), true));
                for (IBuiltInRuleApp builtin : builtins) {
                    if (builtin instanceof OneStepSimplifierRuleApp) {
                        goal.apply(builtin);
                    }
                }
            }
        }

        if(arguments.succedent) {
            for (SequentFormula sf : goal.sequent().succedent()) {
                ImmutableList<IBuiltInRuleApp> builtins = goal.ruleAppIndex().getBuiltInRules(goal, new PosInOccurrence(sf, PosInTerm.getTopLevel(), false));
                for (IBuiltInRuleApp builtin : builtins) {
                    if (builtin instanceof OneStepSimplifierRuleApp) {
                        goal.apply(builtin);
                    }
                }
            }
        }
    }

    @Description("Applies the one-step simplifier to the current goal.")
    public static class Parameters {
        @Option(value = "antecedent", required = false, help = "Apply the one-step simplifier to the antecedent. (bool)")
        public boolean antecedent = true;

        @Option(value = "succedent", required = false, help = "Apply the one-step simplifier to the succedent. (bool)")
        public boolean succedent = true;
    }
}
