package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.feature.FocusIsSubFormulaOfInfFlowContractAppFeature;
import de.uka.ilkd.key.strategy.termfeature.IsPostConditionTermFeature;


/**
 * The macro UseInformationFlowContractMacro applies all applicable information
 * flow contracts.
 * <p/>
 * The rules that are applied can be set in {@link #ADMITTED_RULENAMES}.
 * <p/>
 * @author christoph
 */
public class PrepareInfFlowContractPreBranchesMacro extends StrategyProofMacro {

    private static final String INF_FLOW_RULENAME_PREFIX =
            "Use_information_flow_contract";

    private static final String IMP_LEFT_RULENAME = "impLeft";

    private static final String DOUBLE_IMP_LEFT_RULENAME = "doubleImpLeft";

    private static final String AND_RIGHT_RULENAME = "andRight";

    @Override
    public String getName() {
        return "Prepare information flow pre branches";
    }


    @Override
    public String getDescription() {
        return "Removes the original post condition from information flow " +
               "contract application pre-branches.";
    }


    @Override
    protected Strategy createStrategy(KeYMediator mediator,
                                      PosInOccurrence posInOcc) {
        return new RemovePostStrategy(mediator.getSelectedProof());
    }


    /**
     * This strategy accepts all rule apps for which the rule name starts with a
     * string in the admitted set and rejects everything else.
     */
    protected class RemovePostStrategy extends AbstractFeatureStrategy {

        private final Name NAME = new Name("RemovePostStrategy");


        public RemovePostStrategy(Proof proof) {
            super(proof);
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
            if (name.equals("hide_right")) {
                return applyTF( "b", IsPostConditionTermFeature.INSTANCE ).compute(ruleApp, pio, goal);
            } else if (name.equals(AND_RIGHT_RULENAME)) {
                RuleAppCost andRightCost =
                        FocusIsSubFormulaOfInfFlowContractAppFeature.INSTANCE.compute(ruleApp, pio, goal);
                return andRightCost.add(NumberRuleAppCost.create(1));
            } else {
                return TopRuleAppCost.INSTANCE;
            }
        }


        @Override
        public boolean isApprovedApp(RuleApp app,
                                     PosInOccurrence pio,
                                     Goal goal) {
            String name = app.rule().name().toString();
            if (!name.equals("hide_right")) {
                return true;
            }

            // approve if
            //  - the parent.parent rule application is an information
            //    flow contract rule application,
            //  - the parent rule application is an impLeft rule application
            //    and
            //  - we are in the branch where we have to show the left hand side
            //    of the implication
            if (goal.node().parent() != null &&
                goal.node().parent().parent() != null) {
                Node parent = goal.node().parent();
                return getAppRuleName(parent).equals(IMP_LEFT_RULENAME) &&
                       getAppRuleName(parent.parent()).startsWith(INF_FLOW_RULENAME_PREFIX) &&
                       parent.child(0) == goal.node() ||
                       getAppRuleName(parent).equals(DOUBLE_IMP_LEFT_RULENAME) &&
                       getAppRuleName(parent.parent()).startsWith(INF_FLOW_RULENAME_PREFIX) &&
                       parent.child(2) != goal.node();
            }
            return false;
        }


        private String getAppRuleName(Node parent) {
            RuleApp parentRuleApp = parent.getAppliedRuleApp();
            String parentRuleName = parentRuleApp.rule().name().toString();
            return parentRuleName;
        }


        @Override
        protected RuleAppCost instantiateApp(RuleApp app,
                                             PosInOccurrence pio,
                                             Goal goal) {
            return computeCost(app, pio, goal);
        }
    }

}
