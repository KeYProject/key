/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.rulefilter;


import de.uka.ilkd.key.rule.Rule;

/**
 * Rule filter that selects taclets which are of a specific class
 */
public class ClassRuleFilter implements RuleFilter {

    private final Class<?> c;

    public ClassRuleFilter(Class<?> c) {
        this.c = c;
    }


    public boolean filter(Rule rule) {
        return c.isAssignableFrom(rule.getClass());
    }
}
