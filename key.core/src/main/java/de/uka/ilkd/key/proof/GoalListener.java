/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.SequentChangeInfo;

import org.key_project.util.collection.ImmutableList;

/** interface to be implemented by a goal listener */
public interface GoalListener {

    /**
     * informs the listener about a change that occured to the sequent of goal
     */
    void sequentChanged(Goal source, SequentChangeInfo sci);

    /**
     * Informs the listener that the given goal <code>source</code> has been replaced by the goals
     * <code>newGoals</code> (note that <code>source</code> may be an element of
     * <code>newGoals</code>). The nodes of <code>newGoals</code> are children of the node
     * <code>parent</code>
     */
    void goalReplaced(Goal source, Node parent, ImmutableList<Goal> newGoals);

    /**
     * Informs the listener that the automatic state {@link Goal#isAutomatic()} has changed.
     *
     * @param source The changed {@link Goal}.
     * @param oldAutomatic The old state.
     * @param newAutomatic The new state.
     */
    void automaticStateChanged(Goal source, boolean oldAutomatic, boolean newAutomatic);
}
