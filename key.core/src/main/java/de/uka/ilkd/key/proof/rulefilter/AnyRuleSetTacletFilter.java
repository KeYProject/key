package de.uka.ilkd.key.proof.rulefilter;

import de.uka.ilkd.key.rule.Taclet;

/**
 * Filter that selects taclets that belong to at least one rule set, i.e. taclets that can be
 * applied automatically.
 */
public class AnyRuleSetTacletFilter extends TacletFilter {

    private AnyRuleSetTacletFilter() {
    }

    /**
     * @return true iff <code>taclet</code> should be included in the result
     */
    public boolean filter(Taclet taclet) {
        return !taclet.getRuleSets().isEmpty();
    }

    public final static TacletFilter INSTANCE = new AnyRuleSetTacletFilter();
}
