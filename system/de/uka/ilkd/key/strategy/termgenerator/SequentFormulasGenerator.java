// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Term generator that enumerates the formulas of the current
 * sequent/antecedent/succedent.
 */
public abstract class SequentFormulasGenerator implements TermGenerator {

    protected SequentFormulasGenerator() {}
    
    public static SequentFormulasGenerator antecedent() {
        return new SequentFormulasGenerator () {
            protected Iterator<ConstrainedFormula> generateForIt(Goal goal) {
                return goal.sequent ().antecedent ().iterator ();
            }
        };
    }
    
    public static SequentFormulasGenerator succedent() {
        return new SequentFormulasGenerator () {
            protected Iterator<ConstrainedFormula> generateForIt(Goal goal) {
                return goal.sequent ().succedent ().iterator ();
            }
        };
    }
    
    public static SequentFormulasGenerator sequent() {
        return new SequentFormulasGenerator () {
            protected Iterator<ConstrainedFormula> generateForIt(Goal goal) {
                return goal.sequent ().iterator ();
            }
        };
    }
    
    protected abstract Iterator<ConstrainedFormula> generateForIt(Goal goal);

    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        return new SFIterator ( generateForIt ( goal ) );
    }

    private static class SFIterator implements Iterator<Term> {
        private final Iterator<ConstrainedFormula> forIt;

        public boolean hasNext() {
            return forIt.hasNext ();
        }

        public Term next() {
            return forIt.next ().formula ();
        }

        public SFIterator(Iterator<ConstrainedFormula> forIt) {
            this.forIt = forIt;
        }
        
        /** 
         * throw an unsupported operation exception
         */
        public void remove() {
            throw new UnsupportedOperationException();
        }
        
    }
}
