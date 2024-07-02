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

package de.uka.ilkd.key.strategy.feature;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.LexPathOrdering;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermOrdering;
import de.uka.ilkd.key.proof.Goal;


/**
 * Abstract superclass for features comparing terms (in particular polynomials
 * or monomials) using the term ordering
 */
public abstract class SmallerThanFeature extends BinaryTacletAppFeature {

    private final TermOrdering termOrdering = new LexPathOrdering ();

    protected boolean lessThan(Term t1, Term t2, PosInOccurrence focus, Goal currentGoal) {
        return compare ( t1, t2 ) < 0;
    }

    protected final int compare(Term t1, Term t2) {
        return termOrdering.compare ( t1, t2 );
    }
    
    /**
     * @return <code>true</code> iff each element of <code>list1</code> is
     *         strictly smaller than all elements of <code>list2</code>
     */
    protected final boolean lessThan(ImmutableList<Term> list1, ImmutableList<Term> list2, 
            PosInOccurrence focus, Goal currentGoal) {
        if ( list2.isEmpty () ) return false;
        for (Term aList1 : list1) {
            final Term te1 = aList1;
            for (Term aList2 : list2) {
                if (!lessThan(te1, aList2, focus, currentGoal)) return false;
            }
        }
        return true;
    }

    protected abstract static class Collector {
    
        private ImmutableList<Term> terms = ImmutableSLList.<Term>nil();
    
        protected void addTerm(Term mon) {
            terms = terms.prepend ( mon );
        }
    
        public ImmutableList<Term> getResult() {
            return terms;
        }
        
    }

}