/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.util.collection.ImmutableList;

/**
 * Interface to be implemented by classes in order to customize the goal selection strategy of the
 * automatic prover environment.
 */
public interface GoalChooser {

    /**
     * Initialise this DefaultGoalChooser for use with a given Proof and a list of goals.
     *
     * @param p_proof *param p_goals the initial list of goals
     */
    void init(Proof p_proof, ImmutableList<Goal> p_goals);

    /**
     * @return the next goal a taclet should be applied to
     */
    Goal getNextGoal();

    /**
     * Remove p_goal from selectedList (e.g. no taclet can be applied to p_goal)
     */
    void removeGoal(Goal p_goal);

    /**
     * The given node has become an internal node of the proof tree, and the children of the node
     * are the given goals
     *
     * @param node
     * @param newGoals
     */
    void updateGoalList(Node node, ImmutableList<Goal> newGoals);

}
