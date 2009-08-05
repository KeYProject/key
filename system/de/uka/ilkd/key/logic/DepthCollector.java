// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.*;

/** 
 * This class is used to collect all appearing metavariables and logic
 * variables in a term, together with their maximum term depth. The
 * maximum depth of the term itself is also determined
*/

public class DepthCollector extends Visitor {

    /**
     * Special depths for some operators (used to make numbers and
     * signs flat)
     *
     * Keys: <code>Operator</code>
     *
     * Values: <code>Integer</code>
     */
    //    private HashMap symbolsDepths = new HashMap ();

    /**
     * Map of the current maximum depths of variables
     *
     * Keys: <code>Operator</code>
     *
     * Values: <code>Integer</code>
     */
    private HashMap<Operator, Integer> varDepths = new HashMap<Operator, Integer> ();

    /**
     * Current maximum depth of the term
     */
    private int     termDepth = 0;

    /**
     * Depth of the current position within the term
     */
    private int     curDepth  = 0;

    /**
     * If this is set to a value not zero, we treat the current
     * subterm as flat
     */
    private int     flat      = 0;

    public DepthCollector() {
        
    }
    
    /**
     * is called by the execPostOrder-method of a term
     */  
    public void visit(Term t) {
	Operator op = t.op ();

	if ( op instanceof Metavariable ||
	     op instanceof QuantifiableVariable ) {
	    Integer oldDepth = (Integer)varDepths.get ( op );

	    if ( oldDepth == null || oldDepth.intValue () < curDepth )
		varDepths.put ( op, Integer.valueOf ( curDepth ) );
	}
    }

    /**
     * We current regard each term with a top-level operator within
     * this set to be flat (this should be better established by
     * inserting the symbols used for numbers and characters into the
     * hashmap above)
     */
    private boolean isFlat ( Operator p_op ) {
	return
	    p_op.name().equals(IntegerLDT.NUMBERS_NAME) ||
	    p_op.name().equals(IntegerLDT.CHAR_ID_NAME);
    }

    /**
     * this method is called in execPreOrder and execPostOrder in class Term
     * when entering the subtree rooted in the term subtreeRoot.
     * when the visitor behaviour depends on informations bound to subtrees.
     * @param subtreeRoot root of the subtree which the visitor enters.
     */
    public void subtreeEntered(Term subtreeRoot){
	if ( flat == 0 ) {
	    ++curDepth;
	    if ( curDepth > termDepth )
		termDepth = curDepth;
	}

	if ( isFlat ( subtreeRoot.op () ) )
	    // We treat numbers as flat structures: THIS ONLY WORKS IF
	    // THE NUMBER TERM DOES NOT CONTAIN VARIABLES
	    ++flat;
    }

    /**
     * this method is called in execPreOrder and execPostOrder in class Term
     * when leaving the subtree rooted in the term subtreeRoot.
     * when the visitor behaviour depends on informations bound to subtrees.
     * @param subtreeRoot root of the subtree which the visitor leaves.
     */
    public void subtreeLeft(Term subtreeRoot){
	if ( isFlat ( subtreeRoot.op () ) )
	    // We treat numbers as flat structures: THIS ONLY WORKS IF
	    // THE NUMBER TERM DOES NOT CONTAIN VARIABLES
	    --flat;

	if ( flat == 0 )
	    --curDepth;
    }


    /**
     * @return the maximum depth of a leaf of the term visited
     */
    public int getMaxDepth () {
	return termDepth;
    }

    /**
     * @return the maximum depth of an occurrence of
     * <code>p_var</code>, if this variable has been found, or
     * <code>-1</code>
     */
    public int getMaxDepth ( Operator p_var ) {
	Integer depth = (Integer)varDepths.get ( p_var );
	return depth == null ? -1 : depth.intValue ();
    }

    /**
     * @return an iterator iterating the found variables
     */
    public Iterator<Operator> getVariables () {
	return Collections.unmodifiableSet(varDepths.keySet ()).iterator ();
    }
}
