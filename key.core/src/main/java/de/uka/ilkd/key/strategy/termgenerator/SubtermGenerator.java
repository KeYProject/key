/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.feature.MutableState;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Term generator that enumerates the subterms or subformulas of a given term. Similarly to
 * <code>RecSubTermFeature</code>, a term feature can be given that determines when traversal should
 * be stopped, i.e., when one should not descend further into a term.
 */
public abstract class SubtermGenerator implements TermGenerator {

    private final TermFeature cond;
    private final ProjectionToTerm completeTerm;

    private SubtermGenerator(ProjectionToTerm completeTerm, TermFeature cond) {
        this.cond = cond;
        this.completeTerm = completeTerm;
    }

    /**
     * Left-traverse the subterms of a term in depth-first order. Each term is returned before its
     * proper subterms.
     */
    public static TermGenerator leftTraverse(ProjectionToTerm cTerm, TermFeature cond) {
        return new SubtermGenerator(cTerm, cond) {
            public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal,
                    MutableState mState) {
                return new LeftIterator(getTermInst(app, pos, goal, mState), mState,
                    goal.proof().getServices());
            }
        };
    }

    /**
     * Right-traverse the subterms of a term in depth-first order. Each term is returned before its
     * proper subterms.
     */
    public static TermGenerator rightTraverse(ProjectionToTerm cTerm, TermFeature cond) {
        return new SubtermGenerator(cTerm, cond) {
            public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal,
                    MutableState mState) {
                return new RightIterator(getTermInst(app, pos, goal, mState), mState,
                    goal.proof().getServices());
            }
        };
    }

    protected Term getTermInst(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        return completeTerm.toTerm(app, pos, goal, mState);
    }

    private boolean descendFurther(Term t, MutableState mState, Services services) {
        return !(cond.compute(t, mState, services) instanceof TopRuleAppCost);
    }

    abstract static class SubIterator implements Iterator<Term> {
        protected ImmutableList<Term> termStack;
        protected final MutableState mState;
        protected final Services services;

        public SubIterator(Term t, MutableState mState, Services services) {
            termStack = ImmutableSLList.<Term>nil().prepend(t);
            this.mState = mState;
            this.services = services;
        }

        public boolean hasNext() {
            return !termStack.isEmpty();
        }
    }

    class LeftIterator extends SubIterator {
        public LeftIterator(Term t, MutableState mState, Services services) {
            super(t, mState, services);
        }

        public Term next() {
            final Term res = termStack.head();
            termStack = termStack.tail();

            if (descendFurther(res, mState, services)) {
                for (int i = res.arity() - 1; i >= 0; --i) {
                    termStack = termStack.prepend(res.sub(i));
                }
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

    class RightIterator extends SubIterator {
        public RightIterator(Term t, MutableState mState, Services services) {
            super(t, mState, services);
        }

        public Term next() {
            final Term res = termStack.head();
            termStack = termStack.tail();

            if (descendFurther(res, mState, services)) {
                for (int i = 0; i != res.arity(); ++i) {
                    termStack = termStack.prepend(res.sub(i));
                }
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
