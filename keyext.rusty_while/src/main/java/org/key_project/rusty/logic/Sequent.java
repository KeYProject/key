/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

public class Sequent implements Iterable<SequentFormula> {
    public static final Sequent EMPTY_SEQUENT = NILSequent.INSTANCE;

    /**
     * creates a new Sequent with empty succedent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public static Sequent createAnteSequent(Semisequent ante) {
        if (ante.isEmpty()) {
            return EMPTY_SEQUENT;
        }
        return new Sequent(ante, Semisequent.EMPTY_SEMISEQUENT);
    }

    /**
     * creates a new Sequent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public static Sequent createSequent(Semisequent ante, Semisequent succ) {
        if (ante.isEmpty() && succ.isEmpty()) {
            return EMPTY_SEQUENT;
        }
        return new Sequent(ante, succ);
    }

    /**
     * creates a new Sequent with empty antecedent
     *
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public static Sequent createSuccSequent(Semisequent succ) {
        if (succ.isEmpty()) {
            return EMPTY_SEQUENT;
        }
        return new Sequent(Semisequent.EMPTY_SEMISEQUENT, succ);
    }

    private final Semisequent antecedent;

    private final Semisequent succedent;

    /**
     * must only be called by NILSequent
     *
     */
    private Sequent() {
        antecedent = Semisequent.EMPTY_SEMISEQUENT;
        succedent = Semisequent.EMPTY_SEMISEQUENT;
    }

    /** creates new Sequent with antecedence and succedence */
    private Sequent(Semisequent antecedent, Semisequent succedent) {
        assert !antecedent.isEmpty() || !succedent.isEmpty();
        this.antecedent = antecedent;
        this.succedent = succedent;
    }

    /**
     * Computes the size of the proof sequent recursively (decends to antecedent and succedent).
     *
     * @return the size of the proof sequent as an integer number
     */
    public int size() {
        return antecedent().size() + succedent().size();
    }

    /** returns semisequent of the antecedent to work with */
    public Semisequent antecedent() {
        return antecedent;
    }

    /** returns semisequent of the succedent to work with */
    public Semisequent succedent() {
        return succedent;
    }

    /**
     * String representation of the sequent
     *
     * @return String representation of the sequent
     */
    @Override
    public String toString() {
        return antecedent().toString() + "==>" + succedent().toString();
    }

    @Override
    public @NonNull Iterator<SequentFormula> iterator() {
        return new SequentIterator(antecedent(), succedent());
    }

    /**
     * @param formulaNumber formula number (1-based)
     * @return whether that formula is in the antecedent
     */
    public boolean numberInAntec(int formulaNumber) {
        checkFormulaIndex(formulaNumber);
        return formulaNumber <= antecedent.size();
    }

    /**
     * determines if the sequent is empty.
     *
     * @return true iff the sequent consists of two instances of Semisequent.EMPTY_SEMISEQUENT
     */
    public boolean isEmpty() {
        return antecedent.isEmpty() && succedent.isEmpty();
    }

    /**
     * Get a sequent formula by its position in the sequent.
     * The first formula has number 1.
     *
     * @param formulaNumber formula number
     * @return the sequent formula at that position
     */
    public SequentFormula getFormulaByNr(int formulaNumber) {
        checkFormulaIndex(formulaNumber);
        if (formulaNumber <= antecedent.size()) {
            return antecedent.get(formulaNumber - 1);
        }
        return succedent.get((formulaNumber - 1) - antecedent.size());
    }

    private static final class NILSequent extends Sequent {
        private static final NILSequent INSTANCE = new NILSequent();

        private NILSequent() {
        }

        @Override
        public boolean isEmpty() {
            return true;
        }

        @Override
        public @NonNull Iterator<SequentFormula> iterator() {
            return ImmutableSLList.<SequentFormula>nil().iterator();
        }
    }

    static class SequentIterator implements Iterator<SequentFormula> {

        /**
         * The iterator over the ancedent of the proof sequent.
         */
        private final Iterator<SequentFormula> anteIt;
        /**
         * The iterator over the succedent of the proof sequent.
         */
        private final Iterator<SequentFormula> succIt;

        /**
         * Constructs a new iterator over a proof sequent.
         *
         * @param ante The antecedent of the sequent.
         * @param succ The succedent of the sequent.
         */
        SequentIterator(Semisequent ante, Semisequent succ) {
            this.anteIt = ante.iterator();
            this.succIt = succ.iterator();
        }

        @Override
        public boolean hasNext() {
            return anteIt.hasNext() || succIt.hasNext();
        }

        @Override
        public SequentFormula next() {
            if (anteIt.hasNext()) {
                return anteIt.next();
            }
            return succIt.next();
        }

        /**
         * throw an unsupported operation exception as sequents are immutable
         */
        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    /**
     * Check that the provided formula number is a 1-based index and in bounds.
     * Throws an {@link IllegalArgumentException} otherwise.
     *
     * @param formulaNumber the formula number
     */
    private void checkFormulaIndex(int formulaNumber) {
        if (formulaNumber <= 0 || formulaNumber > size()) {
            throw new IllegalArgumentException(
                "No formula nr. " + formulaNumber + " in seq. " + this);
        }
    }
}
