/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;



import org.key_project.rusty.logic.PosInOccurrence;
import org.key_project.rusty.proof.Goal;

/**
 * Buit-in rule interface. As applications of this rule kind may not be successful in each case one
 * has to ensure that the goal split is done only iff the application was successful.
 */
public interface BuiltInRule extends Rule {

    /**
     * returns true iff a rule is applicable at the given position. This does not necessarily mean
     * that a rule application will change the goal (this decision is made due to performance
     * reasons)
     */
    boolean isApplicable(Goal goal, PosInOccurrence pio);

    boolean isApplicableOnSubTerms();

    // IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services);
}
