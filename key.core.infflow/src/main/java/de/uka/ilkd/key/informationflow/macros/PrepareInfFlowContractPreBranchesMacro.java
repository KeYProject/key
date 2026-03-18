/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.informationflow.FocusIsSubFormulaOfInfFlowContractAppFeature;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.macros.StrategyProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.AbstractFeatureStrategy;
import de.uka.ilkd.key.strategy.Strategy;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;

import org.jspecify.annotations.NonNull;


/**
 * The macro UseInformationFlowContractMacro applies all applicable information flow contracts.
 *
 * @author christoph
 */
public class PrepareInfFlowContractPreBranchesMacro extends StrategyProofMacro {

    private static final String INF_FLOW_RULENAME_PREFIX = "Use_information_flow_contract";

    private static final String IMP_LEFT_RULENAME = "impLeft";

    private static final String DOUBLE_IMP_LEFT_RULENAME = "doubleImpLeft";

    private static final String AND_RIGHT_RULENAME = "andRight";

    @Override
    public String getName() {
        return "Prepare information flow pre branches";
    }

    @Override
    public String getCategory() {
        return "Information Flow";
    }

    @Override
    public String getDescription() {
        return "Removes the original post condition from information flow "
            + "contract application pre-branches.";
    }


    @Override
    protected Strategy<@NonNull Goal> createStrategy(Proof proof,
            PosInOccurrence posInOcc) {
        return new RemovePostStrategy(proof);
    }


    /**
     * This strategy accepts all rule apps for which the rule name starts with a string in the
     * admitted set and rejects everything else.
     */
    protected static class RemovePostStrategy extends AbstractFeatureStrategy {

        private final Name NAME = new Name("RemovePostStrategy");


        public RemovePostStrategy(Proof proof) {
            super(proof);
        }


        @Override
        public @NonNull Name name() {
            return NAME;
        }


        @Override
        public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp ruleApp,
                PosInOccurrence pio, Goal goal,
                MutableState mState) {
            String name = ruleApp.rule().name().toString();
            if (name.equals("hide_right")) {
                return applyTF("b",
                    hasLabel(ParameterlessTermLabel.POST_CONDITION_LABEL))
                        .computeCost(ruleApp, pio,
                            goal, mState);
            } else if (name.equals(AND_RIGHT_RULENAME)) {
                RuleAppCost andRightCost = FocusIsSubFormulaOfInfFlowContractAppFeature.INSTANCE
                        .computeCost(ruleApp, pio, goal, mState);
                return andRightCost.add(NumberRuleAppCost.create(1));
            } else {
                return TopRuleAppCost.INSTANCE;
            }
        }


        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio,
                Goal goal) {
            String name = app.rule().name().toString();
            if (!name.equals("hide_right")) {
                return true;
            }

            // approve if
            // - the parent.parent rule application is an information
            // flow contract rule application,
            // - the parent rule application is an impLeft rule application
            // and
            // - we are in the branch where we have to show the left hand side
            // of the implication
            if (goal.node().parent() != null && goal.node().parent().parent() != null) {
                Node parent = goal.node().parent();
                return getAppRuleName(parent).equals(IMP_LEFT_RULENAME)
                        && getAppRuleName(parent.parent()).startsWith(INF_FLOW_RULENAME_PREFIX)
                        && parent.child(0) == goal.node()
                        || getAppRuleName(parent).equals(DOUBLE_IMP_LEFT_RULENAME)
                                && getAppRuleName(parent.parent()).startsWith(
                                    INF_FLOW_RULENAME_PREFIX)
                                && parent.child(2) != goal.node();
            }
            return false;
        }


        private String getAppRuleName(Node parent) {
            RuleApp parentRuleApp = parent.getAppliedRuleApp();
            String parentRuleName = parentRuleApp.rule().name().toString();
            return parentRuleName;
        }


        @Override
        protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                MutableState mState) {
            return computeCost(app, pio, goal, mState);
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }
    }

}
