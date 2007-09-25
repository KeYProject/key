package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseMethodContractRule;

public class UseMethodContractRuleFilter implements RuleFilter {

    public static final RuleFilter INSTANCE = new UseMethodContractRuleFilter ();
    
    private UseMethodContractRuleFilter () {
    }
    
    public boolean filter(Rule rule) {        
        return (rule instanceof UseMethodContractRule);
    }

}
