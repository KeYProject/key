package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InfFlowPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

import java.util.Set;

/**
 * The macro SelfcompositionStateExpansionMacro applies rules to extract
 * the self-composed states after the merge of the symbolic execution goals
 * which is included in the proof obligation generation from information flow
 * contracts. This macro splits the goal.
 *
 * The rules that are applied can be set in {@link #ADMITTED_RULES}.
 *
 * @author christoph
 */
public class SelfcompositionStateExpansionMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Self-composition state expansion";
    }

    @Override
    public String getDescription() {
        return "Extract the self-composed states after the merge of the "
                + "symbolic execution goals which is included in the proof "
                + "obligation generation from information flow contracts.";
    }

    private static final String[] ADMITTED_RULES = {
        "andLeft", "orLeft", "impRight", "unfold_computed_formula", "andRight"
    };

    private static final String INF_FLOW_UNFOLD_PREFIX = "unfold_computed_formula";

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

    @Override
    protected Strategy createStrategy(KeYMediator mediator, PosInOccurrence posInOcc) {
        return new SelfCompExpansionStrategy(getAdmittedRuleNames());
    }

    @Override
    protected boolean ruleApplicationInContextAllowed(RuleApp ruleApp, PosInOccurrence pio, Goal goal) {
        String ruleName = ruleApp.rule().name().toString();
        if ("andLeft".equals(ruleName) &&
            pio.constrainedFormula().formula().op() instanceof UpdateApplication) {
            return false;
        } else {
            return true;
        }
    }
    

    /**
     * {@inheritDoc}
     *
     * <p>
     * This compound macro is applicable if and only if the first macro is applicable.
     * If there is no first macro, this is not applicable.
     */
    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {

        final Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            return false;
        }
        final Services services = proof.getServices();
        if (services == null) {
            return false;
        }
        final ProofOblInput poForProof =
                services.getSpecificationRepository().getProofOblInput(proof);
        return (poForProof instanceof InfFlowPO) && super.canApplyTo(mediator, goals, posInOcc);
    }

    @Override
    protected boolean allowOSS() {
        return false;
    }

    /**
     * This strategy accepts all rule apps for which the rule name is in the
     * admitted set or has INF_FLOW_UNFOLD_PREFIX as a prefix and rejects everything else.
     */
    private class SelfCompExpansionStrategy implements Strategy {

        private final Name NAME =
                new Name(SelfcompositionStateExpansionMacro.SelfCompExpansionStrategy
                                .class.getSimpleName());

        private final Set<String> admittedRuleNames;

        public SelfCompExpansionStrategy(Set<String> admittedRuleNames) {
            this.admittedRuleNames = admittedRuleNames;
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public RuleAppCost computeCost(RuleApp ruleApp,
                                       PosInOccurrence pio,
                                       Goal goal) {
            String name = ruleApp.rule().name().toString();
            if (    (   admittedRuleNames.contains(name)
                     || name.startsWith(INF_FLOW_UNFOLD_PREFIX))
                 && ruleApplicationInContextAllowed(ruleApp, pio, goal)) {
                JavaCardDLStrategy.Factory strategyFactory =
                        new JavaCardDLStrategy.Factory();
                Strategy javaDlStrategy =
                        strategyFactory.create(goal.proof(),
                                               new StrategyProperties());
                RuleAppCost costs = javaDlStrategy.computeCost(ruleApp, pio, goal);
                if ("orLeft".equals(name)) {
                    costs = costs.add(NumberRuleAppCost.create(100));
                }
                return costs;
            } else {
                return TopRuleAppCost.INSTANCE;
            }
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            return true;
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
        }

    }
}
