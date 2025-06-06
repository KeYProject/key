/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;

import org.jspecify.annotations.NonNull;

/// A [Feature] is a class that is able to compute the cost of a [RuleApp].
@FunctionalInterface
public interface Feature {

    /// Evaluate the cost of a [RuleApp].
    ///
    /// @param app the RuleApp
    /// @param pos position where <code>app</code> is to be applied
    /// @param goal the goal on which <code>app</code> is to be applied
    /// @param mState variable bank / local storage for feature who might require to store temporary
    /// information that changes during computation, e.g. [TermBuffer]s
    /// @return the cost of the rule application expressed as a <code>RuleAppCost</code> object.
    /// <code>TopRuleAppCost.INSTANCE</code> indicates that the rule shall not be applied at
    /// all (it is discarded by the strategy).
    <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos,
            Goal goal, MutableState mState);
}
