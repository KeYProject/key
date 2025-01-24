/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

/**
 * Subclasses must add {@code create} methods
 */
public abstract class Sequent implements Iterable<SequentFormula> {

    private final Semisequent antecedent;
    private final Semisequent succedent;

    /** creates new Sequent of the shape {@code antecedent ==> succedent} */
    protected Sequent(Semisequent antecedent, Semisequent succedent) {
        assert !antecedent.isEmpty() || !succedent.isEmpty();
        this.antecedent = antecedent;
        this.succedent = succedent;
    }

    /** used by NILSequent implementations */
    protected Sequent(Semisequent emptySeq) {
        assert emptySeq.isEmpty();
        this.antecedent = emptySeq;
        this.succedent = emptySeq;
    }

    /**
     * Computes the size of the proof sequent recursively (descends to antecedent and succedent).
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
    public boolean numberInAntecedent(int formulaNumber) {
        checkFormulaIndex(formulaNumber);
        return formulaNumber <= antecedent.size();
    }

    /**
     * Determines if the sequent is empty.
     *
     * @return true iff the sequent contains no formulas
     */
    public boolean isEmpty() {
        return antecedent.isEmpty() && succedent.isEmpty();
    }

    /**
     * Get a sequent formula by its position in the sequent.
     * The first formula has number {@code 1}.
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

    /**
     * adds a formula to the antecedent (or succedent) of the sequent. Depending on the value of
     * first the formulas are inserted at the beginning or end of the ante-/succedent.
     * (NOTICE:Sequent determines index using identity (==) not equality.)
     *
     * @param sequentFormula the {@link SequentFormula} to be added
     * @param inAntecedent boolean selecting the correct {@link Semisequent} where to insert the
     *        formulas.
     *        If set to true, the antecedent is taken otherwise the succedent.
     * @param first boolean if true the formula is added at the beginning of the ante-/succedent,
     *        otherwise to the end
     * @return a {@link SequentChangeInfo} which contains the new sequent and information which
     *         formulas have been added or removed
     */
    public SequentChangeInfo addFormula(SequentFormula sequentFormula, boolean inAntecedent,
            boolean first) {
        final Semisequent seq = inAntecedent ? antecedent : succedent;

        final SemisequentChangeInfo semiCI =
            first ? seq.insertFirst(sequentFormula) : seq.insertLast(sequentFormula);

        return SequentChangeInfo.createSequentChangeInfo(inAntecedent, semiCI,
            composeSequent(inAntecedent, createSemisequent(semiCI.getFormulaList())),
            this);
    }

    /**
     * adds list of formulas to the antecedent (or succedent) of the sequent. Depending on the value
     * of first the formulas are inserted at the beginning or end of the antecedent/succedent.
     * (NOTICE:Sequent determines index using identity (==) not equality.)
     *
     * @param insertions the {@link ImmutableList} of {@link SequentFormula}s to be added
     * @param inAntecedent boolean selecting the correct {@link Semisequent} where to insert the
     *        formulas. If set to true, the antecedent is taken otherwise the succedent.
     * @param first boolean if true the formulas are added at the beginning of the
     *        antecedent/succedent, otherwise to the end
     * @return a {@link SequentChangeInfo} which contains the new sequent and information which
     *         formulas have been added or removed
     */
    public SequentChangeInfo addFormula(ImmutableList<SequentFormula> insertions,
            boolean inAntecedent, boolean first) {

        if (insertions.isEmpty()) {
            return SequentChangeInfo.createSequentChangeInfo(this);
        }

        final Semisequent seq = inAntecedent ? this.antecedent : succedent;

        final SemisequentChangeInfo semiCI =
            first ? seq.insertFirst(insertions) : seq.insertLast(insertions);

        return SequentChangeInfo.createSequentChangeInfo(inAntecedent, semiCI,
            composeSequent(inAntecedent, createSemisequent(semiCI.getFormulaList())),
            this);
    }

    /**
     * replaces the antecedent ({@code inAntecedent} is true) of this sequent by the given
     * {@link Semisequent} similar for the succedent if {@code inAntecedent} is false.
     *
     * @param inAntecedent if the antecedent or succedent shall be replaced
     * @param otherSemisequent the {@link Semisequent} to use
     * @return the resulting sequent
     */
    protected Sequent composeSequent(boolean inAntecedent, Semisequent otherSemisequent) {

        if ((inAntecedent && otherSemisequent == antecedent()) ||
                (!inAntecedent && otherSemisequent == succedent())) {
            return this;
        }

        final var newAntecedent = inAntecedent ? otherSemisequent : antecedent();
        final var newSuccedent = inAntecedent ? succedent() : otherSemisequent;

        if (newAntecedent.isEmpty() && newSuccedent.isEmpty()) {
            return getEmptySequent();
        } else {
            return createSequent(newAntecedent, newSuccedent);
        }
    }

    abstract protected Sequent getEmptySequent();

    abstract protected Sequent createSequent(Semisequent newAntecedent, Semisequent newSuccedent);

    /**
     * Adds a formula to the sequent at the given position.
     * <p>
     * (NOTE: Sequent determines index using identity (==) not equality.)
     * </p>
     *
     * @param sequentFormula a {@link SequentFormula} to be added
     * @param pos a {@link PosInOccurrence} describes position in the sequent
     * @return a {@link SequentChangeInfo} which contains the new sequent and information which
     *         formulas
     *         have been added or removed
     */
    public SequentChangeInfo addFormula(SequentFormula sequentFormula, PosInOccurrence pos) {
        final Semisequent seq = getSemisequent(pos);

        final SemisequentChangeInfo semiCI =
            seq.insert(seq.indexOf(pos.sequentFormula()), sequentFormula);

        return SequentChangeInfo.createSequentChangeInfo(pos.isInAntec(), semiCI,
            composeSequent(pos.isInAntec(),
                createSemisequent(semiCI.getFormulaList())),
            this);
    }

    /**
     * Replaces a formula at the specified index.
     *
     * @param formulaNr where to replace the formula
     * @param replacement the new sequent formula
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo replaceFormula(int formulaNr, SequentFormula replacement) {
        checkFormulaIndex(formulaNr);
        formulaNr--;
        boolean inAntecedent = formulaNr < antecedent.size();

        Semisequent seq = inAntecedent ? antecedent : succedent;
        int idx = inAntecedent ? formulaNr : formulaNr - antecedent.size();

        final SemisequentChangeInfo semiCI = seq.replace(idx, replacement);

        return SequentChangeInfo.createSequentChangeInfo(inAntecedent, semiCI,
            composeSequent(inAntecedent, createSemisequent(semiCI)), this);
    }

    private Semisequent createSemisequent(SemisequentChangeInfo semiCI) {
        return createSemisequent(semiCI.getFormulaList());
    }

    abstract protected Semisequent createSemisequent(final ImmutableList<SequentFormula> formulas);

    /**
     * adds the formulas of list insertions to the sequent starting at position {@code pos}.
     * (NOTE:Sequent
     * determines index using identity (==) not equality.)
     *
     * @param insertions an {@link ImmutableList} of {@link SequentFormula}s with the formulas to be
     *        added
     * @param pos the {@link PosInOccurrence} describing the position where to insert the formulas
     * @return a {@link SequentChangeInfo} which contains the new sequent and information which
     *         formulas
     *         have been added or removed
     */
    public SequentChangeInfo addFormula(ImmutableList<SequentFormula> insertions,
            PosInOccurrence pos) {
        final Semisequent seq = getSemisequent(pos);

        final SemisequentChangeInfo semiCI =
            seq.insert(seq.indexOf(pos.sequentFormula()), insertions);

        return SequentChangeInfo.createSequentChangeInfo(pos.isInAntec(), semiCI,
            composeSequent(pos.isInAntec(), createSemisequent(semiCI)), this);
    }

    /**
     * removes the formula at position {@code pos} (NOTE:Sequent determines index using identity
     * (==) not
     * equality.)
     *
     * @param pos a {@link PosInOccurrence} that describes position in the sequent
     * @return a {@link SequentChangeInfo} which contains the new sequent and information which
     *         formulas
     *         have been added or removed
     */
    public SequentChangeInfo removeFormula(PosInOccurrence pos) {
        final Semisequent seq = getSemisequent(pos);

        final SemisequentChangeInfo semiCI = seq.remove(seq.indexOf(pos.sequentFormula()));

        return SequentChangeInfo.createSequentChangeInfo(pos.isInAntec(),
            semiCI, composeSequent(pos.isInAntec(), createSemisequent(semiCI)), this);
    }

    /**
     * returns the {@link Semisequent} in which the {@link SequentFormula} described by
     * {@link PosInOccurrence} {@code pos} occurs
     */
    private Semisequent getSemisequent(PosInOccurrence pos) {
        return pos.isInAntec() ? antecedent() : succedent();
    }

    /**
     * replaces the formula at position {@code pos} with the head of the given list and adds the
     * remaining
     * list elements to the sequent (NOTE: Sequent determines index using identity (==) not
     * equality.)
     *
     * @param replacements the {@link ImmutableList} of {@link SequentFormula}s whose head replaces
     *        the formula at position {@code pos} and adds the rest of the list behind
     *        the changed formula
     * @param pos a {@link PosInOccurrence} describing the position of the formula to be replaced
     * @return a {@link SequentChangeInfo} which contains the new sequent and information which
     *         formulas
     *         have been added or removed
     */
    public SequentChangeInfo changeFormula(ImmutableList<SequentFormula> replacements,
            PosInOccurrence pos) {
        final SemisequentChangeInfo semiCI = getSemisequent(pos).replace(pos, replacements);
        return SequentChangeInfo.createSequentChangeInfo(pos.isInAntec(),
            semiCI, composeSequent(pos.isInAntec(), createSemisequent(semiCI)), this);
    }

    /**
     * replaces the formula at the given position with another one (NOTICE:Sequent determines index
     * using identity (==) not equality.)
     *
     * @param newCF the SequentFormula replacing the old one
     * @param p a PosInOccurrence describes position in the sequent
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo changeFormula(SequentFormula newCF, PosInOccurrence p) {
        final SemisequentChangeInfo semiCI = getSemisequent(p).replace(p, newCF);

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(), semiCI,
            composeSequent(p.isInAntec(), createSemisequent(semiCI.getFormulaList())),
            this);
    }

    /**
     * Computes the position of the given sequent formula on the proof sequent, starting with one
     * for the very first sequent formula.
     *
     * @param inAntecedent a boolean stating whether we search in the antecedent or the succedent
     * @param sequentFormula the given sequent formula
     * @return an integer strictly greater than zero for the position of the given sequent formula
     *         on the proof sequent.
     */
    public int formulaNumberInSequent(boolean inAntecedent, SequentFormula sequentFormula) {
        int n = inAntecedent ? 0 : antecedent.size();
        final Iterator<SequentFormula> semisequentIterator =
            inAntecedent ? antecedent.iterator() : succedent.iterator();
        while (semisequentIterator.hasNext()) {
            n++;
            if (semisequentIterator.next().equals(sequentFormula)) {
                return n;
            }
        }
        throw new RuntimeException(
            "Ghost formula " + sequentFormula + " in sequent " + this + " [antec=" + inAntecedent
                + "]");
    }

    /**
     * Computes the position of the given {@link PosInOccurrence} on the proof sequent.
     *
     * @param pio the position
     * @return an integer strictly greater than zero for the position of the given sequent formula
     *         on the proof sequent.
     */
    public int formulaNumberInSequent(PosInOccurrence pio) {
        return formulaNumberInSequent(pio.isInAntec(), pio.sequentFormula());
    }

    protected static abstract class NILSequent extends Sequent {

        protected NILSequent(Semisequent emptySemisequent) {
            super(emptySemisequent);
        }

        @Override
        public boolean isEmpty() {
            return true;
        }

        @Override
        public @NonNull Iterator<org.key_project.prover.sequent.SequentFormula> iterator() {
            return ImmutableSLList.<SequentFormula>nil().iterator();
        }
    }

    static class SequentIterator implements Iterator<SequentFormula> {
        /**
         * The iterator over the antecedent of the proof sequent.
         */
        private final Iterator<SequentFormula> antecedentIterator;
        /**
         * The iterator over the succedent of the proof sequent.
         */
        private final Iterator<SequentFormula> succedentIterator;

        /**
         * Constructs a new iterator over a proof sequent.
         *
         * @param antecedent The antecedent of the sequent.
         * @param succedent The succedent of the sequent.
         */
        SequentIterator(Semisequent antecedent, Semisequent succedent) {
            this.antecedentIterator = antecedent.iterator();
            this.succedentIterator = succedent.iterator();
        }

        @Override
        public boolean hasNext() {
            return antecedentIterator.hasNext() || succedentIterator.hasNext();
        }

        @Override
        public SequentFormula next() {
            if (antecedentIterator.hasNext()) {
                return antecedentIterator.next();
            }
            return succedentIterator.next();
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

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof Sequent o1)) {
            return false;
        }
        return antecedent.equals(o1.antecedent) && succedent.equals(o1.succedent);
    }

    /**
     * used to check whether this sequent contains a given sequent formula.
     *
     * @param formula the given formula
     * @return true if this sequent contains the given formula
     */
    public boolean contains(SequentFormula formula) {
        return antecedent().contains(formula) || succedent().contains(formula);
    }

    /**
     * Returns a list containing every {@link SequentFormula} in this sequent.
     *
     * @return a list containing every {@link SequentFormula} in this sequent.
     */
    public ImmutableList<SequentFormula> asList() {
        return antecedent().asList().append(succedent().asList());
    }
}
