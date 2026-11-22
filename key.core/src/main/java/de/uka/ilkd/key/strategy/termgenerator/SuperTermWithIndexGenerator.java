/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.termgenerator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.strategy.costbased.feature.WeakStableCost;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.SuperTermGenerator;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;
import org.key_project.util.collection.ImmutableList;

/**
 * Generates the terms upward a given position, like {@link SuperTermGenerator#upwards}, but
 * returns each ancestor packed with the index of the child on the path as
 * {@code SuperTermGenerated(ancestor, index)}.
 */
@WeakStableCost
public abstract class SuperTermWithIndexGenerator extends SuperTermGenerator {
    private final Services services;
    private final Operator binFunc;

    protected SuperTermWithIndexGenerator(TermFeature cond, Services services) {
        super(cond, services);
        this.services = services;
        final IntegerLDT numbers = services.getTypeConverter().getIntegerLDT();
        this.binFunc = new SuperTermGeneratedOp(numbers);
    }

    public static TermGenerator upwardsWithIndex(TermFeature cond, Services services) {
        return new SuperTermWithIndexGenerator(cond, services) {
        };
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
        public ImmutableList<Sort> argSorts() {
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
