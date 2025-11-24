/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import java.util.Set;

import de.uka.ilkd.key.informationflow.po.AbstractInfFlowPO;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.AbstractPropositionalExpansionMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * The macro SelfcompositionStateExpansionMacro applies rules to extract the self-composed states
 * after the merge of the symbolic execution goals which is included in the proof obligation
 * generation from information flow contracts. This macro splits the goal.
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

    private static final String[] ADMITTED_RULES =
        { "andLeft", "orLeft", "impRight", "unfold_computed_formula", "andRight" };

    private static final String INF_FLOW_UNFOLD_PREFIX = "unfold_computed_formula";

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

    @Override
    protected Strategy<@NonNull Goal> createStrategy(Proof proof,
            PosInOccurrence posInOcc) {
        return new SelfCompExpansionStrategy(getAdmittedRuleNames());
    }

    @Override
    protected boolean ruleApplicationInContextAllowed(RuleApp ruleApp,
            PosInOccurrence pio,
            Goal goal) {
        String ruleName = ruleApp.rule().name().toString();
        return !"andLeft".equals(ruleName)
                || !(pio.sequentFormula().formula().op() instanceof UpdateApplication);
    }


    /**
     * {@inheritDoc}
     *
     * <p>
     * This compound macro is applicable if and only if the first macro is applicable. If there is
     * no first macro, this is not applicable.
     */
    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals,
            PosInOccurrence posInOcc) {

        if (proof == null) {
            return false;
        }
        final Services services = proof.getServices();
        if (services == null) {
            return false;
        }
        final ProofOblInput poForProof =
            services.getSpecificationRepository().getProofOblInput(proof);
        return (poForProof instanceof AbstractInfFlowPO)
                && super.canApplyTo(proof, goals, posInOcc);
    }

    @Override
    protected boolean allowOSS() {
        return false;
    }

    /**
     * This strategy accepts all rule apps for which the rule name is in the admitted set or has
     * INF_FLOW_UNFOLD_PREFIX as a prefix and rejects everything else.
     */
    private class SelfCompExpansionStrategy implements Strategy<Goal> {

        private final Name NAME = new Name(
            SelfcompositionStateExpansionMacro.SelfCompExpansionStrategy.class.getSimpleName());

        private final Set<String> admittedRuleNames;

        public SelfCompExpansionStrategy(Set<String> admittedRuleNames) {
            this.admittedRuleNames = admittedRuleNames;
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public <G extends ProofGoal<@NonNull G>> RuleAppCost computeCost(RuleApp ruleApp,
                PosInOccurrence pio, G p_goal, MutableState mState) {
            final var goal = (Goal) p_goal;
            String name = ruleApp.rule().name().toString();
            if ((admittedRuleNames.contains(name) || name.startsWith(INF_FLOW_UNFOLD_PREFIX))
                    && ruleApplicationInContextAllowed(ruleApp, pio, goal)) {
                JavaCardDLStrategyFactory strategyFactory = new JavaCardDLStrategyFactory();
                Strategy<@NonNull Goal> javaDlStrategy =
                    strategyFactory.create(goal.proof(), new StrategyProperties());
                RuleAppCost costs = javaDlStrategy.computeCost(ruleApp, pio, goal, mState);
                if ("orLeft".equals(name)) {
                    costs = costs.add(NumberRuleAppCost.create(100));
                }
                return costs;
            } else {
                return TopRuleAppCost.INSTANCE;
            }
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio,
                Goal goal) {
            return true;
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

    }
}
