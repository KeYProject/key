// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import java.util.Iterator;

import de.uka.ilkd.key.logic.ldt.AbstractIntegerLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Term ordering, using the names of symbols; following the script
 * "Automatisches Beweisen", Bernhard Beckert, Reiner Haehnle
 */
public class NameTermOrdering implements TermOrdering {

    /**
     * Compare the two given terms
     * @return a number negative, zero or a number positive if
     * <code>p_a</code> is less than, equal, or greater than
     * <code>p_b</code> regarding the ordering given by the
     * implementing class
     */
    public int compare ( Term p_a, Term p_b ) {
	int w = 0;

	if ( p_a.op () == p_b.op () ) {
	    // Compare the subterms
	    if ( p_a.arity () != 0 ) {
		w = compare ( p_a.sub ( 0 ), p_b.sub ( 0 ) );
	    
		if ( w == 0 )
		    return 0;

		int i;
		for ( i = 1; i < p_a.arity (); ++i ) {
		    if ( w * compare ( p_a.sub ( i ), p_b.sub ( i ) ) <= 0 )
			return 0;
		}
	    }
	} else {
	    // Test whether any of the operators is a variable
	    if ( isVar ( p_a ) || isVar ( p_b ) )
		return 0;

	    w = compare ( p_a.op (), p_b.op () );

	    if ( w == 0 )
		return 0;

	    // Compare the free variables of both terms (we are
	    // currently using the existing collector class for
	    // variable depths; this could be implemented more
	    // efficiently)
	    DepthCollector depthsA = new DepthCollector ();
	    DepthCollector depthsB = new DepthCollector ();
	    
	    p_a.execPostOrder ( depthsA );
	    p_b.execPostOrder ( depthsB );
	    
	    if ( w < 0 ) {
		if ( compareVars ( depthsA, depthsB ) >= 0 )
		    return 0;
	    } else if ( w > 0 ) {
		if ( compareVars ( depthsB, depthsA ) >= 0 )
		    return 0;
	    }
	}

	return w;
    }

    /**
     * Compare the two given symbols
     * @return a number negative, zero or a number positive if
     * <code>p_a</code> is less than, equal, or greater than
     * <code>p_b</code>
     */
    private int compare ( Operator p_a, Operator p_b ) {
	if ( p_a != p_b ) {
	    int v = 0;
	    // Search for special symbols
	    {
		Integer w = getWeight ( p_a );
		if ( w == null ) {
		    if ( getWeight ( p_b ) != null )
			return 1;
		} else {
		    v = w.intValue ();
		    w = getWeight ( p_b );
		    if ( w == null )
			return -1;
		    else
			v -= w.intValue ();
		}
	    }

	    if ( v != 0 )
		return v;

	    // program variables are greater than other symbols
	    if ( p_a instanceof IProgramVariable ) {
		if ( !( p_b instanceof IProgramVariable ) )
		    return 1;
	    } else {
		if ( p_b instanceof IProgramVariable )
		    return -1;
	    }

	    // use the names of the symbols
	    v = p_a.name ().toString ().compareTo ( p_b.name ().toString () );

	    if ( v != 0 )
		return v;

	    // HACK: compare the hash values of the two symbols
	    return sign ( p_b.hashCode () - p_a.hashCode () );
	}

	return 0;
    }

    /**
     * Explicit ordering of some symbols (symbols assigned a weight by
     * this method are regarded as smaller than other symbols);
     * symbols are ordered according to their weight
     */
    private Integer getWeight ( Operator p_op ) {
	if ( p_op.name().equals(AbstractIntegerLDT.NUMBERS_NAME) )
	    return new Integer ( 0 );
	if ( p_op.name().equals(AbstractIntegerLDT.CHAR_ID_NAME) )
	    return new Integer ( 1 );
	if ( p_op instanceof Function && 
	     ((Function) p_op).sort() == Sort.NULL)
	    return new Integer ( 2 );
	if ( "TRUE".equals ( p_op.name ().toString () )
             || "FALSE".equals ( p_op.name ().toString () ) )
	    return new Integer ( 3 );
	if ( p_op instanceof SortDependingSymbol )
	    return new Integer ( 10 );

	return null;
    }

    /**
     * @return true iff <code>p</code> is a variable
     */
    private boolean isVar ( Term p ) {
	return
	    p.op () instanceof Metavariable ||
	    p.op () instanceof QuantifiableVariable;
    }

    private int sign ( int p ) {
	if ( p > 0 )
	    return 1;
	else if ( p < 0 )
	    return -1;
	return 0;
    }

    /**
     * @return a negative number, if each variable collected by
     * <code>p_depthsA</code> has also been collected by
     * <code>p_depthsB</code>, zero otherwise
     */
    private int compareVars ( DepthCollector p_depthsA,
			      DepthCollector p_depthsB ) {
	Iterator<Operator> it  = p_depthsA.getVariables ();

	while ( it.hasNext () ) {
	    if ( p_depthsB.getMaxDepth ( it.next () ) == -1 )
		return 0;
	}

	return -1;
    }

}
