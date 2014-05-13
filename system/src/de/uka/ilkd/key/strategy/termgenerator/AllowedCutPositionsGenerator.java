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
import java.util.Stack;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Enumerate potential subformulas of a formula that could be used for a cut
 * (taclet cut_direct). This term-generator does not descend below quantifiers,
 * only below propositional junctors
 */
public class AllowedCutPositionsGenerator implements TermGenerator {

    private AllowedCutPositionsGenerator () {}
    
    public final static TermGenerator INSTANCE = new AllowedCutPositionsGenerator ();
    
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        return new ACPIterator ( pos.constrainedFormula ().formula (),
                              pos.isInAntec () );
    }

    private static class ACPIterator implements Iterator<Term> {
        private final Stack<Object> termStack = new Stack<Object> (); 

        public ACPIterator(Term t, boolean negated) {
            push ( t, negated );
        }

        private void push(Term t, boolean negated) {
            termStack.push ( t );
            termStack.push ( Boolean.valueOf ( negated ) );
        }

        public boolean hasNext() {
            return !termStack.isEmpty ();
        }

        public Term next() {
            final boolean negated = ( (Boolean)termStack.pop () ).booleanValue ();
            final Term res = (Term)termStack.pop ();
            final Operator op = res.op ();
            
            if ( op == Junctor.NOT ) {
                push ( res.sub ( 0 ), !negated );
            } else if ( op == ( negated ? Junctor.OR : Junctor.AND ) ) {
                push ( res.sub ( 0 ), negated );
                push ( res.sub ( 1 ), negated );
            } else if ( negated && op == Junctor.IMP ) {
                push ( res.sub ( 0 ), !negated );
                push ( res.sub ( 1 ), negated );
            }
            
            return res;
        }

        public void remove() {
            throw new UnsupportedOperationException("Remove not supported");
        }
    }
}