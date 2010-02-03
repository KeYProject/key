// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.termgenerator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

public abstract class SuperTermGenerator implements TermGenerator {

    private final TermFeature cond;
    
    protected SuperTermGenerator(TermFeature cond) {
        this.cond = cond;
    }
    
    public static TermGenerator upwards(TermFeature cond) {
        return new SuperTermGenerator ( cond ) {
            protected IteratorOfTerm createIterator(PosInOccurrence focus) {
                return new UpwardsIterator ( focus );
            }
        };
    }
    
    public static TermGenerator upwardsWithIndex(TermFeature cond) {
        return new SuperTermWithIndexGenerator ( cond ) {
            protected IteratorOfTerm createIterator(PosInOccurrence focus) {
                return new UpwardsIterator ( focus );
            }
        };
    }
    
    public IteratorOfTerm generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        return createIterator ( pos );
    }

    protected abstract IteratorOfTerm createIterator(PosInOccurrence focus);
    
    protected Term generateOneTerm(Term superterm, int child) {
        return superterm;
    }

    private boolean generateFurther(Term t) {
        return ! ( cond.compute ( t ) instanceof TopRuleAppCost );
    }

    abstract static class SuperTermWithIndexGenerator extends SuperTermGenerator {
        private Services services;
        private Function binFunc;

        protected SuperTermWithIndexGenerator(TermFeature cond) {
            super ( cond );
        }

        public IteratorOfTerm generate(RuleApp app, PosInOccurrence pos, Goal goal) {
            if ( services == null ) {
                services = goal.proof ().getServices ();
                final IntegerLDT numbers = services.getTypeConverter ().getIntegerLDT ();
                
                binFunc = new RigidFunction
                     ( new Name ( "SuperTermGenerated" ), Sort.ANY,
                       new Sort[] { Sort.ANY, numbers.getNumberSymbol ().sort () } );
            }
            
            return createIterator ( pos );
        }

        protected Term generateOneTerm(Term superterm, int child) {
            final Term index = TermBuilder.DF.zTerm ( services, "" + child );
            return TermBuilder.DF.func ( binFunc, superterm, index );
        }
    }
    
    class UpwardsIterator implements IteratorOfTerm {
        private PosInOccurrence currentPos;

        private UpwardsIterator(PosInOccurrence startPos) {
            this.currentPos = startPos;
        }

        public boolean hasNext() {
            return currentPos != null && !currentPos.isTopLevel ();
        }

        public Term next() {
            final int child = currentPos.getIndex ();
            currentPos = currentPos.up ();
            final Term res = generateOneTerm ( currentPos.subTerm (), child );
            if ( !generateFurther ( res ) ) currentPos = null;
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
