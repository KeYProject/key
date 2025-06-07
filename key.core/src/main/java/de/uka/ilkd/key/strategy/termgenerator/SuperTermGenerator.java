/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.op.SortedOperator;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public abstract class SuperTermGenerator implements TermGenerator<Goal> {

    private final TermFeature cond;

    protected SuperTermGenerator(TermFeature cond) {
        this.cond = cond;
    }

    public static @NonNull TermGenerator<Goal> upwards(TermFeature cond, final Services services) {
        return new SuperTermGenerator(cond) {
            @Override
            protected @NonNull Iterator<Term> createIterator(
                    PosInOccurrence focus,
                    MutableState mState) {
                return new UpwardsIterator(focus, mState, services);
            }
        };
    }

    public static @NonNull TermGenerator<Goal> upwardsWithIndex(TermFeature cond,
            final Services services) {
        return new SuperTermWithIndexGenerator(cond) {
            @Override
            protected @NonNull Iterator<Term> createIterator(
                    PosInOccurrence focus,
                    MutableState mState) {
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
        private Services services;
        private Operator binFunc;

        protected SuperTermWithIndexGenerator(TermFeature cond) {
            super(cond);
        }

        @Override
        public Iterator<Term> generate(RuleApp app,
                PosInOccurrence pos, @NonNull Goal goal,
                MutableState mState) {
            if (services == null) {
                services = goal.proof().getServices();
                final IntegerLDT numbers = services.getTypeConverter().getIntegerLDT();

                binFunc = new SuperTermGeneratedOp(numbers);

                // binFunc = new Function
                // ( new Name ( "SuperTermGenerated" ), Sort.ANY,
                // new Sort[] { Sort.ANY, numbers.getNumberSymbol ().sort () } );
            }

            return createIterator(pos, mState);
        }

        @Override
        protected @NonNull Term generateOneTerm(Term superterm, int child) {
            final var index = services.getTermBuilder().zTerm(String.valueOf(child));
            return services.getTermBuilder().tf().createTerm(binFunc,
                (de.uka.ilkd.key.logic.Term) superterm, index);
        }

        private static class SuperTermGeneratedOp
                implements SortedOperator, Operator, TerminalSyntaxElement {
            private final @NonNull Name NAME;
            private final IntegerLDT numbers;

            public SuperTermGeneratedOp(IntegerLDT numbers) {
                this.numbers = numbers;
                NAME = new Name("SuperTermGenerated");
            }

            @Override
            public @NonNull Name name() {
                return NAME;
            }

            @Override
            public int arity() {
                return 2;
            }

            @Override
            public @NonNull Sort sort(Sort[] sorts) {
                return JavaDLTheory.ANY;
            }

            @Override
            public @NonNull Sort sort() {
                return JavaDLTheory.ANY;
            }

            @Override
            public @NonNull Sort argSort(int i) {
                return JavaDLTheory.ANY;
            }

            @Override
            public @Nullable ImmutableArray<Sort> argSorts() {
                return null;
            }

            @Override
            public boolean bindVarsAt(int n) {
                return false;
            }

            @Override
            public @NonNull Modifier modifier() {
                return Modifier.RIGID;
            }

            @Override
            public boolean isRigid() {
                return true;
            }

            @Override
            public void validTopLevelException(org.key_project.logic.@NonNull Term term)
                    throws TermCreationException {
                if (!(term.arity() == 2 && term.sub(1).sort()
                        .extendsTrans(numbers.getNumberSymbol().sort()))) {
                    throw new TermCreationException(this, term);
                }
            }
        }
    }

    class UpwardsIterator implements Iterator<Term> {
        private @Nullable PosInOccurrence currentPos;
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
