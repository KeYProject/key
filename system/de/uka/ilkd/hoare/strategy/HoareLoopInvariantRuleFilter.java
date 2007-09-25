package de.uka.ilkd.hoare.strategy;

import de.uka.ilkd.hoare.rule.HoareLoopInvariantRule;
import de.uka.ilkd.key.proof.RuleFilter;
import de.uka.ilkd.key.rule.Rule;

public class HoareLoopInvariantRuleFilter implements RuleFilter {

    public static final RuleFilter INSTANCE = new HoareLoopInvariantRuleFilter ();

    private HoareLoopInvariantRuleFilter () {
    }

    public boolean filter(Rule rule) {        
        return (rule instanceof HoareLoopInvariantRule);
    }

}
