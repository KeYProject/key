/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Helper class for managing a list of goals on which rules are applied. The class provides methods
 * for removing a goal, and for updating the internal data structures after a rule has been applied.
 */
public class DepthFirstGoalChooser extends DefaultGoalChooser {
    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.proof.IGoalChooser#getNextGoal()
     */
    public @Nullable Goal getNextGoal() {
        Goal result;

        if (allGoalsSatisfiable) {
            if (nextGoals.isEmpty()) {
                nextGoals = selectedList;
            }

            if (nextGoals.isEmpty()) {
                result = null;
            } else {
                do {
                    result = nextGoals.head();
                    nextGoals = nextGoals.tail();
                } while (result != null && !result.isAutomatic());
            }
        } else {
            ++nextGoalCounter;
            do {
                result = selectedList.isEmpty() ? null : selectedList.head();
                if (result != null && !result.isAutomatic()) {
                    selectedList = selectedList.tail();
                }
            } while (result != null && !result.isAutomatic());
        }
        return result;
    }

    /*
     * protected static IList<Goal> rotateList ( IList<Goal> p_list ) { if ( p_list.isEmpty() )
     * return ImmSLList.<Goal>nil(); return p_list; }
     */
    protected ImmutableList<Goal> insertNewGoals(ImmutableList<Goal> newGoals,
            ImmutableList<Goal> prevGoalList) {

        for (final Goal g : newGoals) {
            if (proof.openGoals().contains(g)) {
                // if (!allGoalsSatisfiable)
                // goalList = goalList.prepend(g);
                // else
                prevGoalList = prevGoalList.prepend(g);
            }
        }
        return prevGoalList;
    }

    @Override
    protected void updateGoalListHelp(Object node, ImmutableList<Goal> newGoals) {
        ImmutableList<Goal> prevGoalList = ImmutableList.nil();
        boolean newGoalsInserted = false;

        nextGoals = ImmutableList.nil();

        // Locate the split point in selectedList using *all* new goals (see below), but only put
        // the automatic ones back to work on.
        final ImmutableList<Goal> automaticNewGoals = newGoals.filter(Goal::isAutomatic);

        // Remove "node" and the goals contained within "newGoals".
        //
        // The split point is the goal the rule was applied to. A splitting rule reuses that goal
        // object for one of its branches (advancing its node), so it may no longer match by node
        // ("node == goal.node()") and has to be found by identity among the new goals instead. That
        // membership test must run against *all* new goals, not only the automatic ones: if the
        // reused goal was disabled (e.g. proof caching disabled the branch it can close by
        // reference), filtering it out first hides the split point, so newGoalsInserted stays false
        // and the *other*, still enabled, new goals are silently dropped from the work list --
        // which
        // stops automatic proof search while work remains.
        while (!selectedList.isEmpty()) {
            final @NonNull Goal goal = selectedList.head();
            selectedList = selectedList.tail();

            if (node == goal.node() || newGoals.contains(goal)) {
                // continue taclet apps at the next goal in list
                nextGoals = selectedList;

                if (!newGoalsInserted) {
                    prevGoalList = insertNewGoals(automaticNewGoals, prevGoalList);
                    newGoalsInserted = true;
                }
            } else {
                prevGoalList = prevGoalList.append(goal);
            }
        }

        while (!prevGoalList.isEmpty()) {
            selectedList = selectedList.append(prevGoalList.head());
            prevGoalList = prevGoalList.tail();
        }
    }
}
