/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;

/**
 * Term generator that enumerates the formulas of the current sequent/antecedent/succedent.
 */
public abstract class SequentFormulasGenerator implements TermGenerator {

    protected SequentFormulasGenerator() {}

    public static SequentFormulasGenerator antecedent() {
        return new SequentFormulasGenerator() {
            protected Iterator<SequentFormula> generateForIt(
                    Goal goal) {
                return goal.sequent().antecedent().iterator();
            }
        };
    }

    public static SequentFormulasGenerator succedent() {
        return new SequentFormulasGenerator() {
            protected Iterator<SequentFormula> generateForIt(
                    Goal goal) {
                return goal.sequent().succedent().iterator();
            }
        };
    }

    public static SequentFormulasGenerator sequent() {
        return new SequentFormulasGenerator() {
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

        public boolean hasNext() {
            return forIt.hasNext();
        }

        public Term next() {
            return forIt.next().formula();
        }

        public SFIterator(Iterator<SequentFormula> forIt) {
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
