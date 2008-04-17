// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.*;


/**
 * Abstract superclass for features comparing terms (in particular polynomials
 * or monomials) using the term ordering
 */
public abstract class SmallerThanFeature extends BinaryTacletAppFeature {

    private final TermOrdering termOrdering = new LexPathOrdering ();

    protected boolean lessThan(Term t1, Term t2) {
        return compare ( t1, t2 ) < 0;
    }

    protected final int compare(Term t1, Term t2) {
        return termOrdering.compare ( t1, t2 );
    }
    
    /**
     * @return <code>true</code> iff each element of <code>list1</code> is
     *         strictly smaller than all elements of <code>list2</code>
     */
    protected final boolean lessThan(ListOfTerm list1, ListOfTerm list2) {
        if ( list2.isEmpty () ) return false;
        final IteratorOfTerm it1 = list1.iterator ();
        while ( it1.hasNext () ) {
            final Term te1 = it1.next ();
            final IteratorOfTerm it2 = list2.iterator ();
            while ( it2.hasNext () ) {
                if ( !lessThan ( te1, it2.next () ) ) return false;
            }
        }
        return true;
    }

    protected abstract static class Collector {
    
        private ListOfTerm terms = SLListOfTerm.EMPTY_LIST;
    
        protected void addTerm(Term mon) {
            terms = terms.prepend ( mon );
        }
    
        public ListOfTerm getResult() {
            return terms;
        }
        
    }

}
