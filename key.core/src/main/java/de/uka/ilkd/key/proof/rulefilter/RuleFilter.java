/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.proof.rulefilter;

import de.uka.ilkd.key.rule.Rule;

/**
 * Interface for objects that represent sets of rules, and which can be used to distinguish
 * different kinds of rules.
 */
public interface RuleFilter {

    boolean filter(Rule rule);

}
