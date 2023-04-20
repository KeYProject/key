package de.uka.ilkd.key.proof.rulefilter;

import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.rule.Rule;

/**
 * Rule filter that selects taclets which are members of a given explicit set
 */
public class SetRuleFilter implements RuleFilter {

    private final HashSet<Rule> set = new LinkedHashSet<>();

    public void addRuleToSet(Rule rule) {
        set.add(rule);
    }

    public boolean filter(Rule rule) {
        return set.contains(rule);
    }

    public boolean isEmpty() {
        return set.isEmpty();
    }
}
