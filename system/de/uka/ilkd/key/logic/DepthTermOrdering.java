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

import java.util.Iterator;

import de.uka.ilkd.key.logic.op.Operator;


/**
 * Term ordering, comparing the maximum depths of terms and contained
 * variables; following definition 5.14 in the script "Automatisches
 * Beweisen", Bernhard Beckert, Reiner Haehnle
 */
public class DepthTermOrdering implements TermOrdering {

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
	else
	    return 0;
    }

    /**
     * @return a negative number, if each variable collected by
     * <code>p_depthsA</code> has also been collected by
     * <code>p_depthsB</code>, and <code>p_depthsB</code> has also
     * found a greater maximum depth for that variable; zero otherwise
     */
    protected int compareVars ( DepthCollector p_depthsA,
				DepthCollector p_depthsB ) {
	Iterator<Operator> it  = p_depthsA.getVariables ();
	Operator           var;
	int                depthB;

	while ( it.hasNext () ) {
	    var    = it.next ();
	    depthB = p_depthsB.getMaxDepth ( var );

	    if ( depthB == -1 || depthB <= p_depthsA.getMaxDepth ( var ) )
		return 0;
	}

	return -1;
    }

}
