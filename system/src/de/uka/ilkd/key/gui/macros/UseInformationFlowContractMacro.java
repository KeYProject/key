package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppFeature;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * The macro UseInformationFlowContractMacro applies all applicable information
 * flow contracts.
 * 
 * The rules that are applied can be set in {@link #ADMITTED_RULENAME_PREFIXES}.
 * 
 * @author christoph
 */
public class UseInformationFlowContractMacro extends StrategyProofMacro {
    
    @Override 
    public String getName() {
        return "Use information flow contract";
    }

    @Override 
    public String getDescription() {
        return "Applies all applicable information flow contract rules.";
    }

    private static final String[] ADMITTED_RULENAME_PREFIXES = {
        "Use_information_flow_contract"
    };

    private static final Set<String> ADMITTED_RULENAME_PREFIX_SET = asSet(ADMITTED_RULENAME_PREFIXES);

    /**
     * Gets the set of admitted rule names.
     * 
     * @return a constant non-<code>null</code> set
     */
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULENAME_PREFIX_SET;
    }
    /*
     * convert a string array to a set of strings 
     */
    protected static Set<String> asSet(String[] strings) {
        return Collections.unmodifiableSet(new HashSet<String>(Arrays.asList(strings)));
    }

    @Override
    protected UseInformationFlowContractMacro.PropExpansionStrategy createStrategy(KeYMediator mediator, PosInOccurrence posInOcc) {
        return new UseInformationFlowContractMacro.PropExpansionStrategy(getAdmittedRuleNames());
    }
    
    /**
     * Checks whether the application of the passed rule is ok in the given
     * context.
     * 
     * @param ruleApp   rule to be applied
     * @param pio       context
     * @param goal      context
     * @return          true if rule may be applied
     */
    protected boolean ruleApplicationInContextAllowed(RuleApp ruleApp, PosInOccurrence pio, Goal goal) {
        return true;
    }

    /**
     * This strategy accepts all rule apps for which the rule name starts with
     * a string in the admitted set and rejects everything else.
     */
    protected class PropExpansionStrategy implements Strategy {

        private final Name NAME = new Name(UseInformationFlowContractMacro.PropExpansionStrategy.class.getSimpleName());

        private final Set<String> admittedRuleNamePrefixes;

        public PropExpansionStrategy(Set<String> admittedRuleNames) {
            this.admittedRuleNamePrefixes = admittedRuleNames;
        }

        @Override 
        public Name name() {
            return NAME;
        }

        @Override 
        public RuleAppCost computeCost(RuleApp ruleApp, PosInOccurrence pio, Goal goal) {
            String name = ruleApp.rule().name().toString();
            if(prefixContainedInAdmittedRuleNamePrefixes(name) &&
                    ruleApplicationInContextAllowed(ruleApp, pio, goal)) {
                return NonDuplicateAppFeature.INSTANCE.compute(
                        ruleApp, pio, goal);
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

        private boolean prefixContainedInAdmittedRuleNamePrefixes(String name) {
            for(String admittedPrefix: admittedRuleNamePrefixes) {
                if (name.startsWith(admittedPrefix)) {
                    return true;
                }
            }
            return false;
        }
    }

}
