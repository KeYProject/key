/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.ArrayDeque;
import java.util.Iterator;

import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

/**
 * Enumerate potential subformulas of a formula that could be used for a cut (taclet cut_direct).
 * This term-generator does not descend below quantifiers, only below propositional junctors
 */
public class AllowedCutPositionsGenerator implements TermGenerator<Goal> {

    private AllowedCutPositionsGenerator() {}

    public final static TermGenerator<Goal> INSTANCE = new AllowedCutPositionsGenerator();

    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
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

        @Override
        public boolean hasNext() {
            return !termStack.isEmpty();
        }

        @Override
        public Term next() {
            final boolean negated = (Boolean) termStack.pop();
            final Term res = (Term) termStack.pop();
            final var op = res.op();

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

        @Override
        public void remove() {
            throw new UnsupportedOperationException("Remove not supported");
        }
    }
}
