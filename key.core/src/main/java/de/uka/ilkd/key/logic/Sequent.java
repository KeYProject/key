/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * This class represents a sequent. A sequent consists of an antecedent and succedent. As a sequent
 * is persistent there is no public constructor.
 * <p>
 * A sequent is created either by using one of the composition methods, that are
 * {@link Sequent#createSequent}, {@link Sequent#createAnteSequent} and
 * {@link Sequent#createSuccSequent} or by inserting formulas directly into
 * {@link Sequent#EMPTY_SEQUENT}.
 */
public class Sequent implements Iterable<Term> {

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
     * adds a formula to the antecedent (or succedent) of the sequent. Depending on the value of
     * first the formulas are inserted at the beginning or end of the ante-/succedent.
     * (NOTICE:Sequent determines index using identy (==) not equality.)
     *
     * @param cf the Term to be added
     * @param antec boolean selecting the correct semisequent where to insert the formulas. If set
     *        to true, the antecedent is taken otherwise the succedent.
     * @param first boolean if true the formula is added at the beginning of the ante-/succedent,
     *        otherwise to the end
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo addFormula(Term cf, boolean antec, boolean first) {

        final Semisequent seq = antec ? antecedent : succedent;

        final SemisequentChangeInfo semiCI = first ? seq.insertFirst(cf) : seq.insertLast(cf);

        return SequentChangeInfo.createSequentChangeInfo(antec, semiCI,
            composeSequent(antec, semiCI.semisequent()), this);
    }

    /**
     * adds a formula to the sequent at the given position. (NOTICE:Sequent determines index using
     * identy (==) not equality.)
     *
     * @param cf a Term to be added
     * @param p a PosInOccurrence describes position in the sequent
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo addFormula(Term cf, PosInOccurrence p) {
        final Semisequent seq = getSemisequent(p);

        final SemisequentChangeInfo semiCI = seq.insert(seq.indexOf(p.sequentLevelFormula()), cf);

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(), semiCI,
            composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /**
     * adds list of formulas to the antecedent (or succedent) of the sequent. Depending on the value
     * of first the formulas are inserted at the beginning or end of the ante-/succedent.
     * (NOTICE:Sequent determines index using identity (==) not equality.)
     *
     * @param insertions the IList<Term> to be added
     * @param antec boolean selecting the correct semisequent where to insert the formulas. If set
     *        to true, the antecedent is taken otherwise the succedent.
     * @param first boolean if true the formulas are added at the beginning of the ante-/succedent,
     *        otherwise to the end
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo addFormula(ImmutableList<Term> insertions, boolean antec,
            boolean first) {

        final Semisequent seq = antec ? antecedent : succedent;

        final SemisequentChangeInfo semiCI =
            first ? seq.insertFirst(insertions) : seq.insertLast(insertions);

        return SequentChangeInfo.createSequentChangeInfo(antec, semiCI,
            composeSequent(antec, semiCI.semisequent()), this);
    }

    /**
     * adds the formulas of list insertions to the sequent starting at position p. (NOTICE:Sequent
     * determines index using identy (==) not equality.)
     *
     * @param insertions a IList<Term> with the formulas to be added
     * @param p the PosInOccurrence describing the position where to insert the formulas
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo addFormula(ImmutableList<Term> insertions,
            PosInOccurrence p) {
        final Semisequent seq = getSemisequent(p);

        final SemisequentChangeInfo semiCI =
            seq.insert(seq.indexOf(p.sequentLevelFormula()), insertions);

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(), semiCI,
            composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /**
     * Replace a formula at the specified index.
     *
     * @param formulaNr where to replace the formula
     * @param replacement the new sequent formula
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo replaceFormula(int formulaNr, Term replacement) {
        checkFormulaIndex(formulaNr);
        formulaNr--;
        boolean inAntec = formulaNr < antecedent.size();

        Semisequent seq = inAntec ? antecedent : succedent;
        int idx = inAntec ? formulaNr : formulaNr - antecedent.size();

        final SemisequentChangeInfo semiCI = seq.replace(idx, replacement);

        return SequentChangeInfo.createSequentChangeInfo(inAntec, semiCI,
            composeSequent(inAntec, semiCI.semisequent()), this);
    }

    /** returns semisequent of the antecedent to work with */
    public Semisequent antecedent() {
        return antecedent;
    }

    /**
     * replaces the formula at the given position with another one (NOTICE:Sequent determines index
     * using identity (==) not equality.)
     *
     * @param newCF the Term replacing the old one
     * @param p a PosInOccurrence describes position in the sequent
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo changeFormula(Term newCF, PosInOccurrence p) {
        final SemisequentChangeInfo semiCI = getSemisequent(p).replace(p, newCF);

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(), semiCI,
            composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /**
     * replaces the formula at position p with the head of the given list and adds the remaining
     * list elements to the sequent (NOTICE:Sequent determines index using identity (==) not
     * equality.)
     *
     * @param replacements the IList<Term> whose head replaces the formula at position p
     *        and adds the rest of the list behind the changed formula
     * @param p a PosInOccurrence describing the position of the formula to be replaced
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo changeFormula(ImmutableList<Term> replacements,
            PosInOccurrence p) {

        final SemisequentChangeInfo semiCI = getSemisequent(p).replace(p, replacements);

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(),
            semiCI, composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /**
     * replaces the antecedent ({@code antec} is true) of this sequent by the given
     * {@link Semisequent} similar for the succedent if {@code antec} is false.
     *
     * @param antec if the antecedent or succedent shall be replaced
     * @param semiSeq the {@link Semisequent} to use
     * @return the resulting sequent
     */
    private Sequent composeSequent(boolean antec, Semisequent semiSeq) {
        if (semiSeq.isEmpty()) {
            if (!antec && antecedent.isEmpty()) {
                return EMPTY_SEQUENT;
            } else if (antec && succedent.isEmpty()) {
                return EMPTY_SEQUENT;
            }
        }

        if ((antec && semiSeq == antecedent) || (!antec && semiSeq == succedent)) {
            return this;
        }

        return new Sequent(antec ? semiSeq : antecedent, antec ? succedent : semiSeq);
    }

    /**
     * determines if the sequent is empty.
     *
     * @return true iff the sequent consists of two instances of Semisequent.EMPTY_SEMISEQUENT
     */
    public boolean isEmpty() {
        return antecedent.isEmpty() && succedent.isEmpty();
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
     * Computes the position of the given sequent formula on the proof sequent, starting with one
     * for the very first sequent formula.
     *
     * @param inAntec a boolean stating whether we search in the antecedent or the succedent
     * @param cfma the given sequent formula
     * @return an integer strictly greater than zero for the position of the given sequent formula
     *         on the proof sequent.
     */
    public int formulaNumberInSequent(boolean inAntec, Term cfma) {
        int n = inAntec ? 0 : antecedent.size();
        final Iterator<Term> formIter =
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

    /**
     * Computes the position of the given {@link PosInOccurrence} on the proof sequent.
     *
     * @param pio the position
     * @return an integer strictly greater than zero for the position of the given sequent formula
     *         on the proof sequent.
     */
    public int formulaNumberInSequent(PosInOccurrence pio) {
        var inAntec = pio.isInAntec();
        var formula = pio.sequentLevelFormula();
        return formulaNumberInSequent(inAntec, formula);
    }

    /**
     * Get a sequent formula by its position in the sequent.
     * The first formula has number 1.
     *
     * @param formulaNumber formula number
     * @return the sequent formula at that position
     */
    public Term getFormulabyNr(int formulaNumber) {
        checkFormulaIndex(formulaNumber);
        if (formulaNumber <= antecedent.size()) {
            return antecedent.get(formulaNumber - 1);
        }
        return succedent.get((formulaNumber - 1) - antecedent.size());
    }

    /**
     * returns the semisequent in which the Term described by PosInOccurrence p lies
     */
    private Semisequent getSemisequent(PosInOccurrence p) {
        return p.isInAntec() ? antecedent() : succedent();
    }

    @Override
    public int hashCode() {
        return antecedent.hashCode() * 17 + succedent.hashCode();
    }

    /**
     * returns iterator about all ConstrainedFormulae of the sequent
     *
     * @return iterator about all ConstrainedFormulae of the sequent
     */
    @Override
    public Iterator<Term> iterator() {
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
     * removes the formula at position p (NOTICE:Sequent determines index using identity (==) not
     * equality.)
     *
     * @param p a PosInOccurrence that describes position in the sequent
     * @return a SequentChangeInfo which contains the new sequent and information which formulas
     *         have been added or removed
     */
    public SequentChangeInfo removeFormula(PosInOccurrence p) {
        final Semisequent seq = getSemisequent(p);

        final SemisequentChangeInfo semiCI = seq.remove(seq.indexOf(p.sequentLevelFormula()));

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(),
            semiCI, composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /**
     * Computes the size of the proof sequent recursively (decends to antecedent and succedent).
     *
     * @return the size of the proof sequent as an integer number
     */
    public int size() {
        return antecedent().size() + succedent().size();
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

    private static final class NILSequent extends Sequent {
        private static final NILSequent INSTANCE = new NILSequent();

        private NILSequent() {
        }

        @Override
        public boolean isEmpty() {
            return true;
        }

        @Override
        public Iterator<Term> iterator() {
            return ImmutableSLList.<Term>nil().iterator();
        }

    }

    static class SequentIterator implements Iterator<Term> {

        /**
         * The iterator over the ancedent of the proof sequent.
         */
        private final Iterator<Term> anteIt;
        /**
         * The iterator over the succedent of the proof sequent.
         */
        private final Iterator<Term> succIt;

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
        public Term next() {
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

    /*
     * Returns names of TermLabels, that occur in term or one of its subterms.
     */
    private static Set<Name> getLabelsForTermRecursively(Term term) {
        Set<Name> result = new HashSet<>();

        if (term.hasLabels()) {
            for (TermLabel label : term.getLabels()) {
                result.add(label.name());
            }
        }

        for (final Term subTerm : term.subs()) {
            result.addAll(getLabelsForTermRecursively(subTerm));
        }

        return result;
    }

    /*
     * Returns names of TermLabels, that occur in this sequent.
     */
    public Set<Name> getOccuringTermLabels() {
        final Set<Name> result = new HashSet<>();
        for (final Term sf : this) {
            result.addAll(getLabelsForTermRecursively(sf));
        }
        return result;
    }

    /**
     * used to check whether this sequent contains a given sequent formula.
     *
     * @param form the given formula
     * @return true if this sequent contains the given formula
     */
    public boolean contains(Term form) {
        return antecedent.contains(form) || succedent.contains(form);
    }

    /**
     * Returns a list containing every {@link Term} in this sequent.
     *
     * @return a list containing every {@link Term} in this sequent.
     */
    public ImmutableList<Term> asList() {
        return antecedent.asList().append(succedent.asList());
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
