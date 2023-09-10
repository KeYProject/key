/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.ArrayDeque;
import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Enumerate potential subformulas of a formula that could be used for a cut (taclet cut_direct).
 * This term-generator does not descend below quantifiers, only below propositional junctors
 */
public class AllowedCutPositionsGenerator implements TermGenerator {

    private AllowedCutPositionsGenerator() {}

    public final static TermGenerator INSTANCE = new AllowedCutPositionsGenerator();

    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        return new ACPIterator(pos.sequentFormula().formula(), pos.isInAntec());
    }

    private static class ACPIterator implements Iterator<Term> {
        private final ArrayDeque<Object> termStack = new ArrayDeque<>();

        public ACPIterator(Term t, boolean negated) {
            push(t, negated);
        }

        private void push(Term t, boolean negated) {
            termStack.push(t);
            termStack.push(negated);
        }

        public boolean hasNext() {
            return !termStack.isEmpty();
        }

        public Term next() {
            final boolean negated = (Boolean) termStack.pop();
            final Term res = (Term) termStack.pop();
            final Operator op = res.op();

            if (op == Junctor.NOT) {
                push(res.sub(0), !negated);
            } else if (op == (negated ? Junctor.OR : Junctor.AND)) {
                push(res.sub(0), negated);
                push(res.sub(1), negated);
            } else if (negated && op == Junctor.IMP) {
                push(res.sub(0), !negated);
                push(res.sub(1), negated);
            }

            return res;
        }

        public void remove() {
            throw new UnsupportedOperationException("Remove not supported");
        }
    }
}
