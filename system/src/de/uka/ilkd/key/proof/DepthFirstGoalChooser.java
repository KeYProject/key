// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;

/**
 * Helper class for managing a list of goals on which rules are applied.
 * The class provides methods for removing a goal, and for updating the internal
 * data structures after a rule has been applied. 
 */
public class DepthFirstGoalChooser extends DefaultGoalChooser {
	/* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.IGoalChooser#getNextGoal()
     */
    public Goal getNextGoal () {
        Goal result;

        if ( allGoalsSatisfiable ) {
            if ( nextGoals.isEmpty () )
                nextGoals = selectedList;

            if ( nextGoals.isEmpty() ) {
                result = null;
            } else {
                result = nextGoals.head ();
                nextGoals = nextGoals.tail ();
            }
        } else {
	    ++nextGoalCounter;    
            result = selectedList.isEmpty () ? null : selectedList.head ();
        }        
        return result;
    }
    /*
    protected static IList<Goal> rotateList ( IList<Goal> p_list ) {
        if ( p_list.isEmpty() )
            return ImmSLList.<Goal>nil();        
        return p_list;
    }
    */
    protected ImmutableList<Goal> insertNewGoals (ImmutableList<Goal> newGoals, ImmutableList<Goal> prevGoalList) {

        for (Goal newGoal : newGoals) {
            final Goal g = newGoal;

            if (proof.openGoals().contains(g)) {
//                if (!allGoalsSatisfiable)
//                    goalList = goalList.prepend(g);
//                else
                    prevGoalList = prevGoalList.prepend(g);
            }
        }
        return prevGoalList;
    }

    protected void updateGoalListHelp ( Node node, ImmutableList<Goal> newGoals ) {
        ImmutableList<Goal> prevGoalList     = ImmutableSLList.<Goal>nil();
        boolean    newGoalsInserted = false;
        
        nextGoals                   = ImmutableSLList.<Goal>nil();

        // Remove "node" and goals contained within "newGoals"
        while ( !selectedList.isEmpty ( )) {
            final Goal goal = selectedList.head ();
            selectedList    = selectedList.tail ();
            
            if ( node == goal.node () || newGoals.contains ( goal ) ) {
                // continue taclet apps at the next goal in list
                nextGoals = selectedList;

                if ( !newGoalsInserted ) {
                    prevGoalList = insertNewGoals ( newGoals, prevGoalList );
                    newGoalsInserted = true;
                }
            } else {
                prevGoalList = prevGoalList.append ( goal );
            }
        }

        while ( !prevGoalList.isEmpty() ) {
            selectedList = selectedList.append( prevGoalList.head () );
            prevGoalList = prevGoalList.tail ();
        }
    }
}