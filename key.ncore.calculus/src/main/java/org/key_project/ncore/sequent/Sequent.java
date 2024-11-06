/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.sequent;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * Subclasses must add {@code create} methods
 */
public abstract class Sequent<SF extends SequentFormula> implements Iterable<SF> {
    private final Semisequent<SF> antecedent;

    private final Semisequent<SF> succedent;

    /** used by NILSequent implementations */
    protected Sequent(Semisequent emptySemisequent) {
        this.antecedent = emptySemisequent;
        this.succedent = emptySemisequent;
    }

    /** creates new Sequent with antecedence and succedence */
    protected Sequent(Semisequent<SF> antecedent, Semisequent<SF> succedent) {
        assert !antecedent.isEmpty() || !succedent.isEmpty();
        this.antecedent = antecedent;
        this.succedent = succedent;
    }

    protected Sequent(Semisequent<SF> emptySeq) {
        assert emptySeq.isEmpty();
        this.antecedent = emptySeq;
        this.succedent = emptySeq;
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
    public Semisequent<SF> antecedent() {
        return antecedent;
    }

    /** returns semisequent of the succedent to work with */
    public Semisequent<SF> succedent() {
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
    public @NonNull Iterator<SF> iterator() {
        return new SequentIterator<>(antecedent(), succedent());
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
    public SF getFormulaByNr(int formulaNumber) {
        checkFormulaIndex(formulaNumber);
        if (formulaNumber <= antecedent.size()) {
            return antecedent.get(formulaNumber - 1);
        }
        return succedent.get((formulaNumber - 1) - antecedent.size());
    }

    /**
     * adds a formula to the antecedent (or succedent) of the sequent. Depending on the value of
     * first the formulas are inserted at the beginning or end of the ante-/succedent.
     * (NOTICE:Sequent determines index using identy (==) not equality.)
     *
     * @param cf the SequentFormula to be added
     * @param antec boolean selecting the correct semisequent where to insert the formulas. If set
     *        to true, the antecedent is taken otherwise the succedent.
     * @param first boolean if true the formula is added at the beginning of the ante-/succedent,
     *        otherwise to the end
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo<SF> addFormula(SF cf, boolean antec, boolean first) {
        final Semisequent<SF> seq = antec ? antecedent : succedent;

        final SemisequentChangeInfo<SF> semiCI = first ? seq.insertFirst(cf) : seq.insertLast(cf);

        return SequentChangeInfo.createSequentChangeInfo(antec, semiCI,
            composeSequent(antec, semiCI.semisequent()), this);
    }

    /**
     * adds list of formulas to the antecedent (or succedent) of the sequent. Depending on the value
     * of first the formulas are inserted at the beginning or end of the ante-/succedent.
     * (NOTICE:Sequent determines index using identity (==) not equality.)
     *
     * @param insertions the IList<SequentFormula> to be added
     * @param antec boolean selecting the correct semisequent where to insert the formulas. If set
     *        to true, the antecedent is taken otherwise the succedent.
     * @param first boolean if true the formulas are added at the beginning of the ante-/succedent,
     *        otherwise to the end
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo<SF> addFormula(ImmutableList<SF> insertions,
            boolean antec,
            boolean first) {

        final Semisequent<SF> seq = antec ? antecedent : succedent;

        final SemisequentChangeInfo<SF> semiCI =
            first ? seq.insertFirst(insertions) : seq.insertLast(insertions);

        return SequentChangeInfo.createSequentChangeInfo(antec, semiCI,
            composeSequent(antec, semiCI.semisequent()), this);
    }

    /**
     * replaces the antecedent ({@code antec} is true) of this sequent by the given
     * {@link Semisequent} similar for the succedent if {@code antec} is false.
     *
     * @param antec if the antecedent or succedent shall be replaced
     * @param semiSeq the {@link Semisequent} to use
     * @return the resulting sequent
     */
    protected abstract Sequent<SF> composeSequent(boolean antec, Semisequent<SF> semiSeq);

    /**
     * adds a formula to the sequent at the given position. (NOTICE:Sequent determines index using
     * identy (==) not equality.)
     *
     * @param cf a SequentFormula to be added
     * @param p a PosInOccurrence describes position in the sequent
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo<SF> addFormula(SF cf, PosInOccurrence p) {
        final Semisequent<SF> seq = getSemisequent(p);

        final SemisequentChangeInfo<SF> semiCI =
            seq.insert(seq.indexOf((SF) p.sequentFormula()), cf);

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(), semiCI,
            composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /**
     * adds the formulas of list insertions to the sequent starting at position p. (NOTICE:Sequent
     * determines index using identy (==) not equality.)
     *
     * @param insertions a IList<SequentFormula> with the formulas to be added
     * @param p the PosInOccurrence describing the position where to insert the formulas
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo<SF> addFormula(ImmutableList<SF> insertions,
            PosInOccurrence p) {
        final Semisequent<SF> seq = getSemisequent(p);

        final SemisequentChangeInfo<SF> semiCI =
            seq.insert(seq.indexOf((SF) p.sequentFormula()), insertions);

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(), semiCI,
            composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /**
     * returns the semisequent in which the SequentFormula described by PosInOccurrence p lies
     */
    private Semisequent<SF> getSemisequent(PosInOccurrence p) {
        return p.isInAntec() ? antecedent() : succedent();
    }

    /**
     * Get a sequent formula by its position in the sequent.
     * The first formula has number 1.
     *
     * @param formulaNumber formula number
     * @return the sequent formula at that position
     */
    public SF getFormulabyNr(int formulaNumber) {
        checkFormulaIndex(formulaNumber);
        if (formulaNumber <= antecedent.size()) {
            return antecedent.get(formulaNumber - 1);
        }
        return succedent.get((formulaNumber - 1) - antecedent.size());
    }

    /**
     * replaces the formula at position p with the head of the given list and adds the remaining
     * list elements to the sequent (NOTICE:Sequent determines index using identity (==) not
     * equality.)
     *
     * @param replacements the IList<SequentFormula> whose head replaces the formula at position p
     *        and adds the rest of the list behind the changed formula
     * @param p a PosInOccurrence describing the position of the formula to be replaced
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo<SF> changeFormula(ImmutableList<SF> replacements,
            PosInOccurrence p) {

        final SemisequentChangeInfo<SF> semiCI = getSemisequent(p).replace(p, replacements);

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(),
            semiCI, composeSequent(p.isInAntec(), semiCI.semisequent()), this);
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
    public SequentChangeInfo<SF> changeFormula(SF newCF, PosInOccurrence p) {
        final SemisequentChangeInfo<SF> semiCI = getSemisequent(p).replace(p, newCF);

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(), semiCI,
            composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /**
     * Computes the position of the given sequent formula on the proof sequent, starting with one
     * for the very first sequent formula.
     *
     * @param inAntec a boolean stating whether we search in the antecedent or the succedent
     * @param cfma the given sequent formula
     * @return an integer strictly greater than zero for the position of the given sequent formula
     *         on the proof sequent.
     */
    public int formulaNumberInSequent(boolean inAntec, SF cfma) {
        int n = inAntec ? 0 : antecedent.size();
        final Iterator<SF> formIter =
            inAntec ? antecedent.iterator() : succedent.iterator();
        while (formIter.hasNext()) {
            n++;
            if (formIter.next().equals(cfma)) {
                return n;
            }
        }
        throw new RuntimeException(
            "Ghost formula " + cfma + " in sequent " + this + " [antec=" + inAntec + "]");
    }

    static class SequentIterator<SF extends SequentFormula> implements Iterator<SF> {

        /**
         * The iterator over the ancedent of the proof sequent.
         */
        private final Iterator<SF> anteIt;
        /**
         * The iterator over the succedent of the proof sequent.
         */
        private final Iterator<SF> succIt;

        /**
         * Constructs a new iterator over a proof sequent.
         *
         * @param ante The antecedent of the sequent.
         * @param succ The succedent of the sequent.
         */
        SequentIterator(Semisequent<SF> ante, Semisequent<SF> succ) {
            this.anteIt = ante.iterator();
            this.succIt = succ.iterator();
        }

        @Override
        public boolean hasNext() {
            return anteIt.hasNext() || succIt.hasNext();
        }

        @Override
        public SF next() {
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

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof Sequent<?> o1)) {
            return false;
        }
        return antecedent.equals(o1.antecedent) && succedent.equals(o1.succedent);
    }
}
