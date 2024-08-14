/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.HasOrigin;
import org.key_project.ncore.rules.RuleAbortException;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * This interface has to be implemented by all classes that want to act as a rule in the calculus.
 */
public interface Rule extends org.key_project.ncore.rules.Rule<Goal, RuleApp>, HasOrigin {

    /**
     * the rule is applied on the given goal using the information of rule application.
     *
     * @param goal    the Goal on which to apply <tt>ruleApp</tt>
     * @param ruleApp the rule application to be executed
     * @return all open goals below \old(goal.node()), i.e. the goals resulting from the rule
     * application
     * @throws RuleAbortException when this rule was aborted
     */
    @NonNull
    ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp)
            throws RuleAbortException;
}
