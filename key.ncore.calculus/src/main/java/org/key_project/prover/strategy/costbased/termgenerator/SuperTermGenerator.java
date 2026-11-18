/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.termgenerator;

import java.util.Iterator;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PIOPathIterator;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.WeakStableCost;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

/**
 * Generates the terms upward a given (usually the find-)position and
 * allows to iterate over those in order to check e.g. whether the
 * position is below an update or quantifier.
 *
 * As it only looks upwards, the computed cost is weak stable
 */
@WeakStableCost
public abstract class SuperTermGenerator implements TermGenerator {

    private final TermFeature cond;
    private final LogicServices services;

    protected SuperTermGenerator(TermFeature cond, LogicServices services) {
        this.cond = cond;
        this.services = services;
    }

    public static TermGenerator upwards(TermFeature cond, LogicServices services) {
        return new SuperTermGenerator(cond, services) {
        };
    }

    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, ProofGoal<?> goal,
            MutableState mState) {
        return new UpwardsIterator(pos, mState);
    }

    protected Term generateOneTerm(Term superterm, int child) {
        return superterm;
    }

    private boolean generateFurther(Term t, MutableState mState) {
        return !(cond.compute(t, mState, services) instanceof TopRuleAppCost);
    }

    private class UpwardsIterator implements Iterator<Term> {
        private final Term[] ancestors;
        private final int[] childIndices;
        private int next;
        private final MutableState mState;

        private UpwardsIterator(PosInOccurrence startPos, MutableState mState) {
            this.mState = mState;
            final int depth = startPos.depth();
            this.ancestors = new Term[depth];
            this.childIndices = new int[depth];
            final PIOPathIterator it = startPos.iterator();
            int i = depth;
            while (it.next() != -1) {
                i--;
                final Term sub = it.getSubTerm();
                assert sub != null : "@AssumeAssertion(nullness): the iterator stands on a subterm";
                ancestors[i] = sub;
                childIndices[i] = it.getChild();
            }
        }

        @Override
        public boolean hasNext() {
            return next < ancestors.length;
        }

        @Override
        public Term next() {
            final Term res = generateOneTerm(ancestors[next], childIndices[next]);
            next++;
            if (!generateFurther(res, mState)) {
                next = ancestors.length;
            }
            return res;
        }

        /**
         * throw an unsupported operation exception as generators do not remove
         */
        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }
}
