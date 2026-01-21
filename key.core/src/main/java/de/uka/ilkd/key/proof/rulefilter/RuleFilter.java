package de.uka.ilkd.key.proof.rulefilter;

import de.uka.ilkd.key.rule.Rule;

/**
 * Interface for objects that represent sets of rules, and which can be used to distinguish
 * different kinds of rules.
 */
public interface RuleFilter {

    boolean filter(Rule rule);

}
