/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.proof.rulefilter;

import java.util.HashSet;
import java.util.LinkedHashSet;

import org.key_project.prover.rules.Rule;

/// Rule filter that selects taclets which are members of a given explicit set
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
