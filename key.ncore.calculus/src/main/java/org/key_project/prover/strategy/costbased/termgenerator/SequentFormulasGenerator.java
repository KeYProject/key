/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termgenerator;

import java.util.Iterator;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;

import org.jspecify.annotations.NonNull;

/// Term generator that enumerates the formulas of the current sequent/antecedent/succedent.
public abstract class SequentFormulasGenerator<Goal extends ProofGoal<@NonNull Goal>>
        implements TermGenerator<Goal> {

    protected SequentFormulasGenerator() {}

    public static <Goal extends ProofGoal<@NonNull Goal>> SequentFormulasGenerator<Goal> antecedent() {
        return new SequentFormulasGenerator<>() {
            protected Iterator<SequentFormula> generateForIt(
                    Goal goal) {
                return goal.sequent().antecedent().iterator();
            }
        };
    }

    public static <Goal extends ProofGoal<@NonNull Goal>> SequentFormulasGenerator<Goal> succedent() {
        return new SequentFormulasGenerator<>() {
            protected Iterator<SequentFormula> generateForIt(
                    Goal goal) {
                return goal.sequent().succedent().iterator();
            }
        };
    }

    public static <Goal extends ProofGoal<@NonNull Goal>> SequentFormulasGenerator<Goal> sequent() {
        return new SequentFormulasGenerator<>() {
            protected Iterator<SequentFormula> generateForIt(
                    Goal goal) {
                return goal.sequent().iterator();
            }
        };
    }

    protected abstract Iterator<SequentFormula> generateForIt(
            Goal goal);

    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        return new SFIterator(generateForIt(goal));
    }

    private static class SFIterator implements Iterator<Term> {
        private final Iterator<SequentFormula> forIt;

        public SFIterator(Iterator<SequentFormula> forIt) {
            this.forIt = forIt;
        }

        public boolean hasNext() {
            return forIt.hasNext();
        }

        public Term next() {
            return forIt.next().formula();
        }

        /// throw an unsupported operation exception
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }
}
