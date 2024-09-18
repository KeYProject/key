/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.proof;

import org.key_project.logic.LogicServices;

/**
 * <p>
 * A proof object provides an interface to the current proof status.
 * It mainly manages the proof goals still to be proven.
 * </p>
 * <p>
 * Implementing classes might decide for a complete explicit proof object like the
 * proof tree for a sequent calculus or just opt to a (non-proof generating) set of
 * goals.
 * </p>
 */
public interface ProofObject<G extends ProofGoal<G>> {
    /**
     * returns an iterable collection of open goals
     *
     * @return collection of {@link ProofGoal}s still to be proven
     */
    Iterable<? extends G> openGoals();

    /**
     * adds a list with new goals
     *
     * @param goals the list of {@link ProofGoal}s to be added
     */
    void add(Iterable<G> goals);

    /**
     * replace a given goal by a list of new goals
     *
     * @param oldGoal the {@link ProofGoal} to be replaced
     * @param newGoals list of {@link ProofGoal}s that replace the old goal
     */
    void replace(G oldGoal, Iterable<G> newGoals);

    /**
     * Close the given goal
     *
     * @param goalToClose the goal to close
     */
    void closeGoal(G goalToClose);

    LogicServices getServices();
}
