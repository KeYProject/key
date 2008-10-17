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

import java.util.Iterator;


/**
 * Helper class for managing a list of goals on which rules are applied.
 * The class provides methods for removing a goal, and for updating the internal
 * data structures after a rule has been applied. 
 */
public class DefaultGoalChooser implements IGoalChooser {
    
    /** the proof that is worked with */
    protected Proof      proof;

    /** list of goals on which the strategy should be applied */
    protected ListOfGoal goalList;

    /** part of goalList that should be worked on next */
    protected ListOfGoal nextGoals;

    /** true iff all goals have satisfiable constraints */
    protected boolean    allGoalsSatisfiable = false;

    /**
     * Subset of the goals to which currently taclets are applied. First this
     * is the list of goals with unsatisfiable constraints, later this is a
     * subset of the goals having inconsistent constraints
     */
    protected ListOfGoal selectedList;

    protected Node       currentSubtreeRoot  = null;

    public DefaultGoalChooser () {
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.IGoalChooser#init(de.uka.ilkd.key.proof.Proof, de.uka.ilkd.key.proof.ListOfGoal)
     */
    public void init ( Proof p_proof, ListOfGoal p_goals ) {
        if(p_proof==null && !(p_goals==null || p_goals.isEmpty())){
            throw new RuntimeException("A not existing proof has goals. This makes no sense.");
        }
        if(p_goals==null||p_goals.isEmpty()){
            //the idea of this case is to reset the object if a proof is abandoned. (To prevent memory leaks)
            allGoalsSatisfiable = true;
        }else{//this is the normal branch
            allGoalsSatisfiable = false;
        }
        currentSubtreeRoot  = null;
        if(p_proof!=proof){
            if(proof!=null){
                proof.removeProofTreeListener(proofTreeListener);
            }
            if(p_proof!=null){
                p_proof.addProofTreeListener(proofTreeListener);
            }
        }
        proof               = p_proof;
        setupGoals ( p_goals );
    }

    protected void setupGoals ( ListOfGoal p_goals ) {
        goalList     = SLListOfGoal.EMPTY_LIST;
        selectedList = SLListOfGoal.EMPTY_LIST;
        nextGoals    = SLListOfGoal.EMPTY_LIST;

        if ( allGoalsSatisfiable ) {
            goalList = p_goals;
            if(currentSubtreeRoot!=null) {
                findMinimalSubtree ( currentSubtreeRoot );
            }
        } else {
            final IteratorOfGoal it = p_goals.iterator ();

            while ( it.hasNext () ) {
                final Goal goal = it.next ();
                
                if ( goal.getClosureConstraint ().isSatisfiable () )
                    goalList     = goalList    .prepend ( goal );
                else
                    selectedList = selectedList.prepend ( goal );
            }

            allGoalsSatisfiable = selectedList.isEmpty ();

            if ( allGoalsSatisfiable )
                findMinimalSubtreeBelow ( proof.root () );
        }
    }

    private ProofTreeObserver proofTreeListener = new ProofTreeObserver();
    
    /**Important when a proof is pruned */
    class ProofTreeObserver extends ProofTreeAdapter{
        /** The proof tree has been pruned under the node mentioned in the
         * ProofTreeEvent.  In other words, that node should no longer
         * have any children now.  Any nodes that were not descendants of
         * that node are unaffected.*/
        public void proofPruned(ProofTreeEvent e) {
            ProofTreeRemovedNodeEvent removeEvent = (ProofTreeRemovedNodeEvent)e;
            currentSubtreeRoot = removeEvent.getNode();
            setupGoals ( proof.getSubtreeGoals(proof.root()) );
        }
    }

    
    protected int nextGoalCounter = 0;
    
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
            if ( nextGoalCounter % 100 == 0 )
	       selectedList = rotateList ( selectedList );

            result = selectedList.isEmpty () ? null : selectedList.head ();
        }

        return result;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.IGoalChooser#removeGoal(de.uka.ilkd.key.proof.Goal)
     */
    public void removeGoal ( Goal p_goal ) {
	selectedList = selectedList.removeAll ( p_goal );
	nextGoals    = SLListOfGoal.EMPTY_LIST;
    
	if ( selectedList.isEmpty () ) setupGoals ( goalList );
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.IGoalChooser#updateGoalList(de.uka.ilkd.key.proof.Node, de.uka.ilkd.key.proof.ListOfGoal)
     */
    public void updateGoalList ( Node node, ListOfGoal newGoals ) {
        if ( newGoals.isEmpty ()
                || (newGoals.tail ().isEmpty () && newGoals
                        .head ().node () == node)) {
            // Goals (may) have been closed, remove them from the goal lists
            removeClosedGoals ();
        } else {
            updateGoalListHelp ( node, newGoals );
        }

        if (proof.openGoals ().isEmpty())
            // proof has been closed
            nextGoals = selectedList = goalList = SLListOfGoal.EMPTY_LIST;
        else {
            if ( selectedList.isEmpty ()
                    || (currentSubtreeRoot != null 
                            && isSatisfiableSubtree ( currentSubtreeRoot )) )
                setupGoals ( goalList.prepend ( selectedList ) );
        }
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
                prevGoalList = prevGoalList.prepend ( goal );
            }
        }

        while ( !prevGoalList.isEmpty() ) {
            selectedList = selectedList.prepend( prevGoalList.head () );
            prevGoalList = prevGoalList.tail ();
        }
    }

    protected ListOfGoal insertNewGoals (ListOfGoal newGoals, ListOfGoal prevGoalList) {
        final IteratorOfGoal it = newGoals.iterator ();
        
        while ( it.hasNext () ) {
            final Goal g = it.next ();
            
            if (proof.openGoals ().contains ( g )) {
                if ( !allGoalsSatisfiable
                        && g.getClosureConstraint ()
                                .isSatisfiable () )
                    goalList = goalList.prepend ( g );
                else
                    prevGoalList = prevGoalList.prepend ( g );
            }
        }
        return prevGoalList;
    }


    protected static ListOfGoal rotateList ( ListOfGoal p_list ) {
        if ( p_list.isEmpty() )
            return SLListOfGoal.EMPTY_LIST;
        
        return p_list.tail ().append ( p_list.head () );
    }
    
    protected void removeClosedGoals () {
        boolean        changed = false;
        IteratorOfGoal it      = goalList.iterator ();
        goalList               = SLListOfGoal.EMPTY_LIST;

        while (it.hasNext ()) {
            final Goal goal = it.next ();
            if (proof.openGoals ().contains ( goal )) 
                // order of goals is not relevant
                goalList = goalList.prepend ( goal );
        }

        it = selectedList.iterator ();
        ListOfGoal newList = SLListOfGoal.EMPTY_LIST;

        while ( it.hasNext () ) {
            final Goal goal = it.next ();
            if ( proof.openGoals ().contains ( goal ) ) {
                if ( !allGoalsSatisfiable
                        && goal.getClosureConstraint ().isSatisfiable () ) {
                    goalList = goalList.prepend ( goal );
                    changed = true;
                } else
                    newList = newList.prepend ( goal );
            } else
                changed = true;
        }

        if ( changed ) {
            nextGoals = SLListOfGoal.EMPTY_LIST;

            // for "selectedList", order does matter
            it = newList.iterator ();
            selectedList = SLListOfGoal.EMPTY_LIST;
            while ( it.hasNext () )
                selectedList = selectedList.prepend ( it.next () );
        }
    }

    /**
     * Search for a minimal subtree of the proof tree which is not
     * closable (constraints of its goals are inconsistent) below
     * p_startNode
     *
     * PRECONDITION: * !isSatisfiableSubtree ( p_startNode )
     *               * all goals have satisfiable constraints
     *
     * @return true iff a non-empty subtree was found
     */
    protected boolean findMinimalSubtreeBelow ( Node p_startNode ) {
        Node node = p_startNode;

        while ( node.childrenCount () == 1 )
            node = node.child ( 0 );

        Iterator<Node> childrenIt = node.childrenIterator ();

        while ( childrenIt.hasNext () ) {
            final Node child = childrenIt.next ();

            if (!isSatisfiableSubtree ( child )
                    && findMinimalSubtreeBelow ( child ))
                return true;
        }

        currentSubtreeRoot = p_startNode;
        childrenIt         = node.leavesIterator ();

        while ( childrenIt.hasNext () ) {
            final Node child = childrenIt.next ();
            final Goal goal  = proof.getGoal ( child );

            if ( goalList.contains ( goal ) ) {
                selectedList = selectedList.prepend   ( goal );
                goalList     = goalList    .removeAll ( goal );
            }
        }

        return !selectedList.isEmpty();

    }

    
    /**
     * Search for a minimal subtree of the proof tree which is not
     * closable (constraints of its goals are inconsistent) starting
     * at p_startNode
     *
     * PRECONDITION: all goals have satisfiable constraints
     */
    protected void findMinimalSubtree ( Node p_startNode ) {
	while ( isSatisfiableSubtree ( p_startNode ) )
	    p_startNode = p_startNode.parent ();

	if ( !findMinimalSubtreeBelow ( p_startNode ) )
	    findMinimalSubtreeBelow ( proof.root () );
    }


    protected boolean isSatisfiableSubtree ( Node p_root ) {
	return p_root.getBranchSink ().getResetConstraint ().isSatisfiable ();
    }


}
