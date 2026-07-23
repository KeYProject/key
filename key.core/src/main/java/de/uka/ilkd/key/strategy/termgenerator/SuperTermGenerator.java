/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.WeakStableCost;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;
import org.key_project.util.collection.ImmutableArray;

// Generates the find's ANCESTOR terms (upwards from the find position). The connectives along the
// find path are stable for a surviving application, but a generated ancestor term as a whole also
// carries the siblings of that path, which an independent rewrite can change while the find subterm
// survives. So a feature summing over these ancestors is fixed only while the find FORMULA is
// unchanged -- weakly stable, not fully stable.
@WeakStableCost
public abstract class SuperTermGenerator implements TermGenerator<Goal> {

    private final TermFeature cond;

    protected SuperTermGenerator(TermFeature cond) {
        this.cond = cond;
    }

    public static TermGenerator<Goal> upwards(TermFeature cond, final Services services) {
        return new SuperTermGenerator(cond) {
            @Override
            protected Iterator<Term> createIterator(
                    PosInOccurrence focus, MutableState mState) {
                return new UpwardsIterator(focus, mState, services);
            }
        };
    }

    public static TermGenerator<Goal> upwardsWithIndex(TermFeature cond, final Services services) {
        return new SuperTermWithIndexGenerator(cond, services) {
            @Override
            protected Iterator<Term> createIterator(
                    PosInOccurrence focus, MutableState mState) {
                return new UpwardsIterator(focus, mState, services);
            }
        };
    }

    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos,
            Goal goal,
            MutableState mState) {
        return createIterator(pos, mState);
    }

    protected abstract Iterator<Term> createIterator(
            PosInOccurrence focus, MutableState mState);

    protected Term generateOneTerm(Term superterm, int child) {
        return superterm;
    }

    private boolean generateFurther(Term t, MutableState mState, Services services) {
        return !(cond.compute(t, mState, services) instanceof TopRuleAppCost);
    }

    abstract static class SuperTermWithIndexGenerator extends SuperTermGenerator {
        // Both are fixed at construction from the proof's services (one generator is built per
        // proof and shared by all goals). They used to be lazily filled by generate(), which runs
        // during proof search: under the multi-core prover several workers raced that lazy write,
        // and binFunc is a freshly created operator, so a worker could read a half-initialised or
        // foreign operator. Computing them once in the constructor removes the race; the value is
        // unchanged, since goal.proof().getServices() is the same services the strategy was built
        // with.
        private final Services services;
        private final Operator binFunc;

        protected SuperTermWithIndexGenerator(TermFeature cond, Services services) {
            super(cond);
            this.services = services;
            final IntegerLDT numbers = services.getTypeConverter().getIntegerLDT();
            this.binFunc = new SuperTermGeneratedOp(numbers);
        }

        @Override
        public Iterator<Term> generate(RuleApp app,
                PosInOccurrence pos, Goal goal,
                MutableState mState) {
            return createIterator(pos, mState);
        }

        @Override
        protected Term generateOneTerm(Term superterm, int child) {
            final var index = services.getTermBuilder().zTerm(String.valueOf(child));
            return services.getTermBuilder().tf().createTerm(binFunc,
                (JTerm) superterm, index);
        }

        private static class SuperTermGeneratedOp
                implements SortedOperator, TerminalSyntaxElement, Operator {
            private final Name NAME;
            private final IntegerLDT numbers;

            public SuperTermGeneratedOp(IntegerLDT numbers) {
                this.numbers = numbers;
                NAME = new Name("SuperTermGenerated");
            }

            @Override
            public Name name() {
                return NAME;
            }

            @Override
            public int arity() {
                return 2;
            }

            @Override
            public Sort sort(Sort[] sorts) {
                return JavaDLTheory.ANY;
            }

            @Override
            public Sort sort() {
                return JavaDLTheory.ANY;
            }

            @Override
            public Sort argSort(int i) {
                return JavaDLTheory.ANY;
            }

            @Override
            public ImmutableArray<Sort> argSorts() {
                return null;
            }

            @Override
            public boolean bindVarsAt(int n) {
                return false;
            }

            @Override
            public Modifier modifier() {
                return Modifier.RIGID;
            }

            @Override
            public boolean isRigid() {
                return true;
            }

            @Override
            public void validTopLevelException(Term term)
                    throws TermCreationException {
                if (!(term.arity() == 2 && term.sub(1).sort()
                        .extendsTrans(numbers.getNumberSymbol().sort()))) {
                    throw new TermCreationException(this, term);
                }
            }
        }
    }

    class UpwardsIterator implements Iterator<Term> {
        private PosInOccurrence currentPos;
        private final MutableState mState;
        private final Services services;

        private UpwardsIterator(PosInOccurrence startPos, MutableState mState, Services services) {
            this.currentPos = startPos;
            this.mState = mState;
            this.services = services;
        }

        @Override
        public boolean hasNext() {
            return currentPos != null && !currentPos.isTopLevel();
        }

        @Override
        public Term next() {
            final int child = currentPos.getIndex();
            currentPos = currentPos.up();
            final Term res = generateOneTerm(currentPos.subTerm(), child);
            if (!generateFurther(res, mState, services)) {
                currentPos = null;
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
