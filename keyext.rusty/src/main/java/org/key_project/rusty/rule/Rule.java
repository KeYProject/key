/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Named;
import org.key_project.ncore.rules.RuleAbortException;
import org.key_project.rusty.proof.Goal;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public interface Rule extends org.key_project.ncore.rules.Rule<@NonNull Goal, @NonNull RuleApp>, Named {
    /**
     * the rule is applied on the given goal using the information of rule application.
     *
     * @param goal the Goal on which to apply <tt>ruleApp</tt>
     * @param ruleApp the rule application to be executed
     * @return all open goals below \old(goal.node()), i.e. the goals resulting from the rule
     *         application
     * @throws org.key_project.ncore.rules.RuleAbortException when this rule was aborted
     */
    @NonNull
    ImmutableList<Goal> apply(@NonNull Goal goal, @NonNull RuleApp ruleApp)
            throws RuleAbortException;

    /**
     * returns the display name of the rule
     */
    String displayName();
}
