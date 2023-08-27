/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.rulefilter;

import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.rule.Rule;

/**
 * Rule filter that selects taclets which are members of a given explicit set
 */
public class SetRuleFilter implements RuleFilter {

    private final HashSet<Rule> set;

    public SetRuleFilter() {
        this.set = new LinkedHashSet<>();
    }

    private SetRuleFilter(HashSet<Rule> set) {
        this.set = set;
    }

    public SetRuleFilter copy() {
        return new SetRuleFilter(new LinkedHashSet<>(this.set));
    }

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
