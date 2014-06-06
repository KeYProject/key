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

package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

public abstract class SuperTermGenerator implements TermGenerator {

    private final TermFeature cond;
    
    protected SuperTermGenerator(TermFeature cond) {
        this.cond = cond;
    }
    
    public static TermGenerator upwards(TermFeature cond, final Services services) {
        return new SuperTermGenerator ( cond ) {
            protected Iterator<Term> createIterator(PosInOccurrence focus) {
                return new UpwardsIterator ( focus, services );
            }
        };
    }
    
    public static TermGenerator upwardsWithIndex(TermFeature cond, final Services services) {
        return new SuperTermWithIndexGenerator ( cond ) {
            protected Iterator<Term> createIterator(PosInOccurrence focus) {
                return new UpwardsIterator ( focus, services );
            }
        };
    }
    
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        return createIterator ( pos );
    }

    protected abstract Iterator<Term> createIterator(PosInOccurrence focus);
    
    protected Term generateOneTerm(Term superterm, int child) {
        return superterm;
    }

    private boolean generateFurther(Term t, Services services) {
        return ! ( cond.compute ( t, services ) instanceof TopRuleAppCost );
    }

    abstract static class SuperTermWithIndexGenerator extends SuperTermGenerator {
        private Services services;
        private Operator binFunc;

        protected SuperTermWithIndexGenerator(TermFeature cond) {
            super ( cond );
        }

        public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
            if ( services == null ) {
                services = goal.proof ().getServices ();
                final IntegerLDT numbers = services.getTypeConverter ().getIntegerLDT ();
                
                binFunc = new SortedOperator() {
                    private final Name NAME = new Name("SuperTermGenerated");
                    public Name name() {
                	return NAME;
                    }
                    
                    public int arity() {
                	return 2;
                    }

                    public Sort sort(ImmutableArray<Term> terms) {
                	return Sort.ANY;
                    }
                    
                    public Sort sort() {
                	return Sort.ANY;
                    }
                    
                    public Sort argSort(int i) {
                	return Sort.ANY;
                    }
                    
                    public ImmutableArray<Sort> argSorts () {
                	return null;
                    }

                    public boolean bindVarsAt(int n) {
                	return false;
                    }

                    public boolean isRigid() {
                	return true;
                    }

                    public boolean validTopLevel(Term term) {
                	return term.arity() == 2
                	       && term.sub(1).sort().extendsTrans(numbers.getNumberSymbol ().sort ());
                    }

                    public MatchConditions match(SVSubstitute subst, 
                	    			 MatchConditions mc, 
                	    			 Services services) {
                	return subst == this ? mc : null;
                    }    
                };
                
//                binFunc = new Function
//                     ( new Name ( "SuperTermGenerated" ), Sort.ANY,
//                       new Sort[] { Sort.ANY, numbers.getNumberSymbol ().sort () } );
            }
            
            return createIterator ( pos );
        }

        protected Term generateOneTerm(Term superterm, int child) {
            final Term index = services.getTermBuilder().zTerm ( "" + child );
            return services.getTermBuilder().tf().createTerm( binFunc, superterm, index );
        }
    }
    
    class UpwardsIterator implements Iterator<Term> {
        private PosInOccurrence currentPos;
        
        private final Services services;

        private UpwardsIterator(PosInOccurrence startPos, Services services) {
            this.currentPos = startPos;
            this.services = services;
        }

        public boolean hasNext() {
            return currentPos != null && !currentPos.isTopLevel ();
        }

        public Term next() {
            final int child = currentPos.getIndex ();
            currentPos = currentPos.up ();
            final Term res = generateOneTerm ( currentPos.subTerm (), child );
            if ( !generateFurther ( res, services ) ) currentPos = null;
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