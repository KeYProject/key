package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.tacletbuilder.RemovePostTacletBuilder;
import de.uka.ilkd.key.strategy.*;


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


    @Override
    public String getName() {
        return "Prepare information flow pre branches";
    }


    @Override
    public String getDescription() {
        return "Removes the original post condition form information flow " +
               "contract application pre-branches.";
    }


    @Override
    protected Strategy createStrategy(KeYMediator mediator,
                                      PosInOccurrence posInOcc) {
        return new RemovePostStrategy();
    }


    /**
     * This strategy accepts all rule apps for which the rule name starts with a
     * string in the admitted set and rejects everything else.
     */
    protected class RemovePostStrategy implements Strategy {

        private final Name NAME =
                new Name(PrepareInfFlowContractPreBranchesMacro.RemovePostStrategy.class.getSimpleName());


        public RemovePostStrategy() {
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
            String removePostName =
                    RemovePostTacletBuilder.REMOVE_POST_RULENAME.toString();
            if (name.startsWith(removePostName)) {
                return LongRuleAppCost.ZERO_COST;
            } else {
                return TopRuleAppCost.INSTANCE;
            }
        }


        @Override
        public boolean isApprovedApp(RuleApp app,
                                     PosInOccurrence pio,
                                     Goal goal) {
            // abort if
            //  - the parent.parent rule application is an information
            //    flow contract rule application,
            //  - the parent rule application is an impLeft rule applicatoin
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
        public void instantiateApp(RuleApp app,
                                   PosInOccurrence pio,
                                   Goal goal,
                                   RuleAppCostCollector collector) {
        }
    }

}
