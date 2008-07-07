// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

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
    protected static ListOfGoal rotateList ( ListOfGoal p_list ) {
        if ( p_list.isEmpty() )
            return SLListOfGoal.EMPTY_LIST;        
        return p_list;
    }
    */
    protected ListOfGoal insertNewGoals (ListOfGoal newGoals, ListOfGoal prevGoalList) {
        final IteratorOfGoal it = newGoals.iterator ();
        
        while ( it.hasNext () ) {
            final Goal g = it.next ();
            
            if (proof.openGoals ().contains ( g )) {
                if ( !allGoalsSatisfiable
                        && g.getClosureConstraint ()
                                .isSatisfiable () )
                    goalList = goalList.prepend( g );
                else
                    prevGoalList = prevGoalList.prepend ( g );
            }
        }
        return prevGoalList;
    }

    protected void updateGoalListHelp ( Node node, ListOfGoal newGoals ) {
        ListOfGoal prevGoalList     = SLListOfGoal.EMPTY_LIST;
        boolean    newGoalsInserted = false;
        
        nextGoals                   = SLListOfGoal.EMPTY_LIST;

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
