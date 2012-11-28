package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.feature.InfFlowContractAppFeature;
import de.uka.ilkd.key.strategy.feature.InfFlowImpFeature;
import de.uka.ilkd.key.util.properties.Properties;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;


/**
 * The macro UseInformationFlowContractMacro applies all applicable information
 * flow contracts.
 * <p/>
 * The rules that are applied can be set in {@link #ADMITTED_RULENAMES}.
 * <p/>
 * @author christoph
 */
public class UseInformationFlowContractMacro extends StrategyProofMacro {

    @Override
    public String getName() {
        return "Use information flow contracts";
    }


    @Override
    public String getDescription() {
        return "Applies all applicable information flow contract rules.";
    }
    private static final String INF_FLOW_RULENAME_PREFIX =
            "Use_information_flow_contract";

    private static final String IMP_LEFT_RULENAME = "impLeft";

    private static final String[] ADMITTED_RULENAMES = {
        "andLeft"
    };

    private static final Set<String> ADMITTED_RULENAME_SET =
            asSet(ADMITTED_RULENAMES);


    /**
     * Gets the set of admitted rule names.
     * <p/>
     * @return a constant non-
     * <code>null</code> set
     */
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULENAME_SET;
    }
    /*
     * convert a string array to a set of strings
     */


    protected static Set<String> asSet(String[] strings) {
        return Collections.unmodifiableSet(new HashSet<String>(Arrays.asList(strings)));
    }


    @Override
    protected UseInformationFlowContractMacro.PropExpansionStrategy createStrategy(
            KeYMediator mediator,
            PosInOccurrence posInOcc) {
        return new UseInformationFlowContractMacro.PropExpansionStrategy(getAdmittedRuleNames());
    }


    /**
     * Checks whether the application of the passed rule is ok in the given
     * context.
     * <p/>
     * @param ruleApp rule to be applied
     * @param pio     context
     * @param goal    context
     * @return true if rule may be applied
     */
    protected boolean ruleApplicationInContextAllowed(RuleApp ruleApp,
                                                      PosInOccurrence pio,
                                                      Goal goal) {
        return true;
    }


    /**
     * This strategy accepts all rule apps for which the rule name starts with a
     * string in the admitted set and rejects everything else.
     */
    protected class PropExpansionStrategy implements Strategy {

        public final Properties.Property<Boolean> STOP_INF_FLOW_CONTRACT_APPL_PROPERTY =
                new Properties.Property<Boolean>(Boolean.class,
                                                 "Stop information flow contract " +
                                                 "applicaton property");

        private final Name NAME =
                new Name(UseInformationFlowContractMacro.PropExpansionStrategy.class.getSimpleName());

        private final Set<String> admittedRuleNames;


        public PropExpansionStrategy(Set<String> admittedRuleNames) {
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
            // first try to apply
            //  - impLeft on previous information flow contract application
            //    formula, else
            //  - try to apply information flow contract, else
            //  - try to apply other allowed rules (andLeft)
            String name = ruleApp.rule().name().toString();
            if (name.startsWith(INF_FLOW_RULENAME_PREFIX) &&
                ruleApplicationInContextAllowed(ruleApp, pio, goal)) {
                return InfFlowContractAppFeature.INSTANCE.compute(
                        ruleApp, pio, goal);
            } else if (name.equals(IMP_LEFT_RULENAME)) {
                return InfFlowImpFeature.INSTANCE.compute(ruleApp, pio, goal);
            } else if (admittedRuleNames.contains(name) &&
                       ruleApplicationInContextAllowed(ruleApp, pio, goal)) {
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
                RuleApp parentRuleApp = parent.getAppliedRuleApp();
                String parentRuleName = parentRuleApp.rule().name().toString();
                Node parentParent = parent.parent();
                RuleApp parentParentRuleApp = parentParent.getAppliedRuleApp();
                String parentParentRuleName =
                        parentParentRuleApp.rule().name().toString();
                if (parentRuleName.equals(IMP_LEFT_RULENAME) &&
                    parentParentRuleName.startsWith(INF_FLOW_RULENAME_PREFIX) &&
                    parent.child(0) == goal.node()) {
                    return false;
                }
            }

            return true;
        }


        @Override
        public void instantiateApp(RuleApp app,
                                   PosInOccurrence pio,
                                   Goal goal,
                                   RuleAppCostCollector collector) {
        }
    }

}
