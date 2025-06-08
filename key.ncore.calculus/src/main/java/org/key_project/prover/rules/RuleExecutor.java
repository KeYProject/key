/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public interface RuleExecutor<Goal extends @NonNull ProofGoal<Goal>> {

    /// applies the given rule application to the specified goal
    ///
    /// @param goal the goal that the rule application should refer to.
    /// @param ruleApp the rule application that is executed.
    /// @return List of the goals created by the rule which have to be proved. If this is a
    /// close-goal-taclet ( this.closeGoal () ), the first goal of the return list is the
    /// goal that should be closed (with the constraint this taclet is applied under).
    ImmutableList<@NonNull Goal> apply(@NonNull Goal goal, @NonNull RuleApp ruleApp);
}
