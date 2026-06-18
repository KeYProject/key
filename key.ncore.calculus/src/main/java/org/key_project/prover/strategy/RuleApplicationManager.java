/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;

import org.jspecify.annotations.Nullable;


/// This interface provides the next rule application to be applied to the
/// main loop of the prover.
///
/// Rule application managers are associated with a specific proof goal.
/// Each proof goal has its own copy of a manager (see [#copy()]).
///
public interface RuleApplicationManager<G extends @Nullable ProofGoal<G>> extends NewRuleListener {

    /// Clear existing caches of applicable rules
    void clearCache();

    /// @return the first applicable rule app, i.e. the least expensive element of the heap that is
    /// not obsolete and caches the result of this operation to save some time the next time
    /// the method nextAndCache() or next() is called. A call of next() empties the cache
    /// again.
    RuleApp peekNext();

    /// @return the next rule that is supposed to be applied
    RuleApp next();

    /// Set the goal <code>this</code> is the rule app manager for
    void setGoal(G p_goal);

    /// Copies this rule application manager.
    ///
    /// @return copy of this manager
    RuleApplicationManager<G> copy();
}
