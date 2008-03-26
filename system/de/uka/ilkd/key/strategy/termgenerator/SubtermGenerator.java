// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.termgenerator;

import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

/**
 * Term generator that enumerates the subterms or subformulas of a given term.
 * Similarly to <code>RecSubTermFeature</code>, a term feature can be given
 * that determines when traversal should be stopped, i.e., when one should not
 * descend further into a term.
 */
public abstract class SubtermGenerator implements TermGenerator {

    private final TermFeature cond;
    private final ProjectionToTerm completeTerm;

    private SubtermGenerator(ProjectionToTerm completeTerm, TermFeature cond) {
        this.cond = cond;
        this.completeTerm = completeTerm;
    }
    
    /**
     * Left-traverse the subterms of a term in depth-first order. Each term is
     * returned before its proper subterms.
     */
    public static TermGenerator leftTraverse(ProjectionToTerm cTerm,
                                             TermFeature cond) {
        return new SubtermGenerator (cTerm, cond) {
            public IteratorOfTerm generate(RuleApp app, PosInOccurrence pos, Goal goal) {
                return new LeftIterator ( getTermInst ( app, pos, goal ) );
            }
        };
    }

    /**
     * Right-traverse the subterms of a term in depth-first order. Each term is
     * returned before its proper subterms.
     */
    public static TermGenerator rightTraverse(ProjectionToTerm cTerm,
                                              TermFeature cond) {
        return new SubtermGenerator (cTerm, cond) {
            public IteratorOfTerm generate(RuleApp app, PosInOccurrence pos, Goal goal) {
                return new RightIterator ( getTermInst ( app, pos, goal ) );
            }
        };
    }

    protected Term getTermInst(RuleApp app, PosInOccurrence pos, Goal goal) {
        return completeTerm.toTerm ( app, pos, goal );
    }
    
    private boolean descendFurther(Term t) {
        return ! ( cond.compute ( t ) instanceof TopRuleAppCost );
    }
        
    abstract class Iterator implements IteratorOfTerm {
        protected ListOfTerm termStack;

        public Iterator(Term t) {
            termStack = SLListOfTerm.EMPTY_LIST.prepend ( t );
        }

        public boolean hasNext() {
            return !termStack.isEmpty ();
        }
    }

    class LeftIterator extends Iterator {
        public LeftIterator(Term t) {
            super ( t );
        }

        public Term next() {
            final Term res = termStack.head ();
            termStack = termStack.tail ();
            
            if ( descendFurther ( res ) ) {
                for ( int i = res.arity () - 1; i >= 0; --i )
                    termStack = termStack.prepend ( res.sub ( i ) );
            }
            
            return res;
        }

        /** 
         * throw an unsupported operation exception as generators do not remove
         */
        public void remove() {
            throw new UnsupportedOperationException();
        }
   
    }

    class RightIterator extends Iterator {
        public RightIterator(Term t) {
            super ( t );
        }

        public Term next() {
            final Term res = termStack.head ();
            termStack = termStack.tail ();
            
            if ( descendFurther ( res ) ) {
                for ( int i = 0; i != res.arity (); ++i )
                    termStack = termStack.prepend ( res.sub ( i ) );
            }
            
            return res;
        }
        
        /** 
         * throw an unsupported operation exception as generators do not remove
         */
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }
}
