/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.MutableState;

import org.jspecify.annotations.NonNull;

/**
 * Term generator that enumerates the formulas of the current sequent/antecedent/succedent.
 */
public abstract class SequentFormulasGenerator implements TermGenerator {

    protected SequentFormulasGenerator() {}

    public static @NonNull SequentFormulasGenerator antecedent() {
        return new SequentFormulasGenerator() {
            protected @NonNull Iterator<SequentFormula> generateForIt(@NonNull Goal goal) {
                return goal.sequent().antecedent().iterator();
            }
        };
    }

    public static @NonNull SequentFormulasGenerator succedent() {
        return new SequentFormulasGenerator() {
            protected @NonNull Iterator<SequentFormula> generateForIt(@NonNull Goal goal) {
                return goal.sequent().succedent().iterator();
            }
        };
    }

    public static @NonNull SequentFormulasGenerator sequent() {
        return new SequentFormulasGenerator() {
            protected @NonNull Iterator<SequentFormula> generateForIt(@NonNull Goal goal) {
                return goal.sequent().iterator();
            }
        };
    }

    protected abstract Iterator<SequentFormula> generateForIt(Goal goal);

    public @NonNull Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        return new SFIterator(generateForIt(goal));
    }

    private static class SFIterator implements Iterator<Term> {
        private final Iterator<SequentFormula> forIt;

        public boolean hasNext() {
            return forIt.hasNext();
        }

        public @NonNull Term next() {
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
