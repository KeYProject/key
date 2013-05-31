// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.ImmutableList;

/**
 * Interface to be implemented by classes in order to customize the goal selection
 * strategy of the automatic prover environment.
 */
public interface IGoalChooser {

    /**
     * Initialise this DefaultGoalChooser for use with a given Proof and a list of goals.
     * @param p_proof
     * *param p_goals the initial list of goals
     */
    public abstract void init(Proof p_proof, ImmutableList<Goal> p_goals);

    /**
     * @return the next goal a taclet should be applied to
     */
    public abstract Goal getNextGoal();

    /**
     * Remove p_goal from selectedList (e.g. no taclet can be applied to
     * p_goal)
     */
    public abstract void removeGoal(Goal p_goal);

    /**
     * The given node has become an internal node of the proof tree, and the
     * children of the node are the given goals
     * @param node
     * @param newGoals
     */
    public abstract void updateGoalList(Node node, ImmutableList<Goal> newGoals);

}
