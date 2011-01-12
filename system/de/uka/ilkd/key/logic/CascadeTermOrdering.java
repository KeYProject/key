// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

/**
 * Combine two term orderings: if two terms are unrelated, regarding
 * ordering <code>orderingA</code>, then <code>orderingB</code> is
 * used (nb: this will usually NOT result in an ordering, for which *
 * substitutions are monotonic)
 */
public class CascadeTermOrdering implements TermOrdering {

    private TermOrdering orderingA;
    private TermOrdering orderingB;

    public CascadeTermOrdering ( TermOrdering p_orderingA,
				 TermOrdering p_orderingB ) {
	orderingA = p_orderingA;
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
	int w = orderingA.compare ( p_a, p_b );

	if ( w == 0 )
	    return orderingB.compare ( p_a, p_b );

	return w;
    }

}
