/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.rules;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.ncore.proof.ProofGoal;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public interface Rule<G extends @NonNull ProofGoal<G>, App extends RuleApp<G>> extends Named {
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
    ImmutableList<G> apply(G goal, App ruleApp)
            throws RuleAbortException;

    /**
     * the name of the rule
     */
    @NonNull Name name();

    /**
     * returns the display name of the rule
     */
    default String displayName() {
        return name().toString();
    }
}
