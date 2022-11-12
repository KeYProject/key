/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
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
