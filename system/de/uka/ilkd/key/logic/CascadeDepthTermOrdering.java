// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import java.util.Iterator;

import de.uka.ilkd.key.logic.op.Operator;


/**
 * Term ordering, comparing the maximum depths of terms and contained
 * variables; following definition 5.14 in the script "Automatisches
 * Beweisen", Bernhard Beckert, Reiner Haehnle
 *
 * This ordering has the possibility to refer to a secundary ordering
 * upon terms having the same depths (i.e. both the same maximal depth
 * and maximal variable depths); this guarantees substitutions to stay
 * monotonic
 */
public class CascadeDepthTermOrdering extends DepthTermOrdering {

    /**
     * secundary ordering
     */
    private TermOrdering orderingB;

    public CascadeDepthTermOrdering ( TermOrdering p_orderingB ) {
	orderingB = p_orderingB;
    }

    /**
     * Compare the two given terms
     * @return a number negative, zero or a number positive if
     * <code>p_a</code> is less than, equal, or greater than
     * <code>p_b</code> regarding the ordering given by the
     * implementing class
     */
    public int compare ( Term p_a, Term p_b ) {
	DepthCollector depthsA = new DepthCollector ();
	DepthCollector depthsB = new DepthCollector ();

	p_a.execPostOrder ( depthsA );
	p_b.execPostOrder ( depthsB );

	if ( depthsA.getMaxDepth () < depthsB.getMaxDepth () )
	    return compareVars ( depthsA, depthsB );
	else if ( depthsB.getMaxDepth () < depthsA.getMaxDepth () )
	    return - compareVars ( depthsB, depthsA );
	else if ( equalVars ( depthsA, depthsB ) )
	    return orderingB.compare ( p_a, p_b );
	return 0;
    }

    /**
     * @return true, iff each variable collected by
     * <code>p_depthsA</code> has also been collected by
     * <code>p_depthsB</code> with the same maximum depth
     */
    private boolean equalVars ( DepthCollector p_depthsA,
				DepthCollector p_depthsB ) {
	return
	    equalVarsHelp ( p_depthsA, p_depthsB ) &&
	    equalVarsHelp ( p_depthsB, p_depthsA );
    }

    private boolean equalVarsHelp ( DepthCollector p_depthsA,
				    DepthCollector p_depthsB ) {
	Iterator<Operator> it  = p_depthsA.getVariables ();
	Operator           var;

	while ( it.hasNext () ) {
	    var = it.next ();

	    if ( p_depthsA.getMaxDepth ( var ) !=
		 p_depthsB.getMaxDepth ( var ) )
		return false;
	}

	return true;
    }

}
