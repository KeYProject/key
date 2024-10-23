/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.ncore.rules.RuleAbortException;
import org.key_project.ncore.rules.RuleExecutor;
import org.key_project.ncore.sequent.PosInOccurrence;
import org.key_project.rusty.proof.Goal;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * Buit-in rule interface. As applications of this rule kind may not be successful in each case one
 * has to ensure that the goal split is done only iff the application was successful.
 */
public interface BuiltInRule extends Rule, RuleExecutor {
    /**
     * the rule is applied on the given goal using the information of rule application.
     *
     * @param goal the Goal on which to apply <tt>ruleApp</tt>
     * @param ruleApp the rule application to be executed
     * @return all open goals below \old(goal.node()), i.e. the goals resulting from the rule
     *         application
     * @throws RuleAbortException when this rule was aborted
     */
    @NonNull
    ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp)
            throws RuleAbortException;

    @Override
    default RuleExecutor getExecutor() {
        return this;
    }

    /**
     * returns true iff a rule is applicable at the given position. This does not necessarily mean
     * that a rule application will change the goal (this decision is made due to performance
     * reasons)
     */
    boolean isApplicable(Goal goal, PosInOccurrence pio);

    boolean isApplicableOnSubTerms();

    // IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services);
}
