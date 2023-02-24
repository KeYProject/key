package de.uka.ilkd.key.proof.rulefilter;

import de.uka.ilkd.key.rule.Rule;

/**
 * Inversion of a rule filter
 */
public class NotRuleFilter implements RuleFilter {

    private final RuleFilter a;

    public NotRuleFilter(RuleFilter p_a) {
        a = p_a;
    }

    public boolean filter(Rule rule) {
        return !a.filter(rule);
    }

    public String toString() {
        return "Not:" + a;
    }

}
