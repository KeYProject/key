/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.rule.Rule;

/**
 * Simple data object to store a mapping of rules to various counters.
 *
 * @author Arne Keller
 */
public class RuleStatistics {
    /**
     * Mapping of rule name to number of proof steps that used this rule, the number of proof steps
     * that used this rule and didn't contribute to the proof ("useless" proof steps), and the
     * number of "useless" proof steps that initiate a chain of further (useless) proof steps.
     */
    private final Map<String, RuleStatisticData> map = new HashMap<>();
    /**
     * Mapping of rule name to whether this rule introduces new proof branches.
     */
    private final Map<String, Boolean> ruleBranched = new HashMap<>();

    /**
     * Register one rule application (proof step).
     *
     * @param rule the rule
     * @param branches whether this rule application creates new proof branches
     */
    public void addApplication(Rule rule, boolean branches) {
        String name = rule.displayName();
        ruleBranched.put(name, branches);

        var entry = map.computeIfAbsent(name, it -> new RuleStatisticData(it, 0, 0, 0));
        map.put(name, new RuleStatisticData(name, entry.first + 1, entry.second, entry.third));
    }

    /**
     * Register a useless rule application (proof step).
     *
     * @param rule the rule
     * @param branches whether this rule application creates new proof branches
     */
    public void addUselessApplication(Rule rule, boolean branches) {
        String name = rule.displayName();
        ruleBranched.put(name, branches);

        var entry = map.computeIfAbsent(name, it -> new RuleStatisticData(it, 0, 0, 0));
        map.put(name, new RuleStatisticData(name, entry.first + 1, entry.second + 1, entry.third));
    }

    /**
     * Register an "initial useless" rule application (proof step).
     *
     * @param rule the rule
     * @param branches whether this rule application creates new proof branches
     */
    public void addInitialUselessApplication(Rule rule, boolean branches) {
        String name = rule.displayName();
        ruleBranched.put(name, branches);

        var entry = map.computeIfAbsent(name, it -> new RuleStatisticData(it, 0, 0, 0));
        map.put(name,
            new RuleStatisticData(name, entry.first + 1, entry.second + 1, entry.third + 1));
    }

    /**
     * Get the total counts sorted by a comparison function.
     * The comparator receives: the rule name, the number of rule applications, the number of
     * useless applications and the number of "initial useless" applications.
     *
     * @param comparator custom comparator
     * @return list of rule names + counters
     */
    public List<RuleStatisticData> sortBy(Comparator<? super RuleStatisticData> comparator) {
        return map.values().stream()
                .sorted(comparator)
                .toList();
    }

    /**
     * @param rule rule display name
     * @return whether that rule creates new branches
     */
    public boolean branches(String rule) {
        return ruleBranched.get(rule);
    }

    public record RuleStatisticData(String ruleName, int first, int second, int third) {
    }
}
