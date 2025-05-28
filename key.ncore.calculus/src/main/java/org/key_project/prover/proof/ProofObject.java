/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.proof;

import org.key_project.logic.LogicServices;

import org.jspecify.annotations.Nullable;

/// A proof object provides an interface to the current proof status.
/// It mainly manages the proof goals still to be proven.
///
///
/// Implementing classes might decide for a complete explicit proof object like the
/// proof tree for a sequent calculus or just opt to a (non-proof generating) set of
/// goals.
///
public interface ProofObject<G extends ProofGoal<@Nullable G>> {
    /// returns an iterable collection of open goals
    ///
    /// @return collection of [ProofGoal]s still to be proven
    Iterable<? extends G> openGoals();

    /// adds a list with new goals
    ///
    /// @param goals the list of [ProofGoal]s to be added
    void add(Iterable<G> goals);

    /// replace a given goal by a list of new goals
    ///
    /// @param oldGoal the [ProofGoal] to be replaced
    /// @param newGoals list of [ProofGoal]s that replace the old goal
    void replace(G oldGoal, Iterable<G> newGoals);

    /// Close the given goal
    ///
    /// @param goalToClose the goal to close
    void closeGoal(G goalToClose);

    /// returns true iff the specified property could be proven valid and the proof has been closed
    ///
    /// @return true if the proof (i.e., all its goals) have been closed
    boolean closed();

    /// returns the services which provide access to the meta infrastructure like
    /// namespaces for functions, sort etc.
    ///
    /// @return services managing the logic infrastructure
    LogicServices getServices();
}
