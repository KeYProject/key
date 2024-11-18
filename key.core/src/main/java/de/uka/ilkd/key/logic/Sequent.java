/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.logic.Name;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

/**
 * This class represents a sequent. A sequent consists of an antecedent and succedent. As a sequent
 * is persistent there is no public constructor.
 * <p>
 * A sequent is created either by using one of the composition methods, that are
 * {@link Sequent#createSequent}, {@link Sequent#createAnteSequent} and
 * {@link Sequent#createSuccSequent} or by inserting formulas directly into
 * {@link Sequent#EMPTY_SEQUENT}.
 */
public class Sequent extends org.key_project.prover.sequent.Sequent<SequentFormula> {
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

    /**
     * must only be called by NILSequent
     *
     */
    private Sequent() {
        super(Semisequent.EMPTY_SEMISEQUENT, Semisequent.EMPTY_SEMISEQUENT);
    }

    /** creates new Sequent with antecedence and succedence */
    private Sequent(Semisequent antecedent, Semisequent succedent) {
        super(antecedent, succedent);
    }

    @Override
    public Semisequent succedent() {
        return (Semisequent) super.succedent();
    }

    @Override
    public Semisequent antecedent() {
        return (Semisequent) super.antecedent();
    }

    @Override
    public SequentChangeInfo<SequentFormula> removeFormula(PosInOccurrence p) {
        return super.removeFormula(p);
    }

    /**
     * replaces the antecedent ({@code antec} is true) of this sequent by the given
     * {@link Semisequent} similar for the succedent if {@code antec} is false.
     *
     * @param antec if the antecedent or succedent shall be replaced
     * @param p_semiSeq the {@link Semisequent} to use
     * @return the resulting sequent
     */
    protected Sequent composeSequent(boolean antec,
            org.key_project.prover.sequent.Semisequent<SequentFormula> p_semiSeq) {
        final var semiSeq = (Semisequent) p_semiSeq;
        if (semiSeq.isEmpty()) {
            if (!antec && antecedent().isEmpty()) {
                return EMPTY_SEQUENT;
            } else if (antec && succedent().isEmpty()) {
                return EMPTY_SEQUENT;
            }
        }

        if ((antec && semiSeq == antecedent()) || (!antec && semiSeq == succedent())) {
            return this;
        }
        final Semisequent semiSequent = (Semisequent) semiSeq;
        return new Sequent(antec ? semiSequent : antecedent, antec ? succedent : semiSequent);
    }

    /**
     * determines if the sequent is empty.
     *
     * @return true iff the sequent consists of two instances of Semisequent.EMPTY_SEMISEQUENT
     */
    public boolean isEmpty() {
        return antecedent().isEmpty() && succedent().isEmpty();
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
    public int formulaNumberInSequent(boolean inAntec, SequentFormula cfma) {
        int n = inAntec ? 0 : antecedent.size();
        final Iterator<SequentFormula> formIter =
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
        var formula = pio.sequentFormula();
        return formulaNumberInSequent(inAntec, formula);
    }

    /**
     * Get a sequent formula by its position in the sequent.
     * The first formula has number 1.
     *
     * @param formulaNumber formula number
     * @return the sequent formula at that position
     */
    public SequentFormula getFormulabyNr(int formulaNumber) {
        checkFormulaIndex(formulaNumber);
        if (formulaNumber <= antecedent.size()) {
            return antecedent.get(formulaNumber - 1);
        }
        return succedent.get((formulaNumber - 1) - antecedent.size());
    }

    /**
     * returns the semisequent in which the SequentFormula described by PosInOccurrence p lies
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
    public Iterator<SequentFormula> iterator() {
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

        final SemisequentChangeInfo semiCI = seq.remove(seq.indexOf(p.sequentFormula()));

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

    /**
     * returns true iff the given variable is bound in a formula of a SequentFormula in this
     * sequent.
     *
     * @param v the bound variable to search for
     */
    public boolean varIsBound(QuantifiableVariable v) {
        for (SequentFormula sequentFormula : this) {
            final BoundVarsVisitor bvv = new BoundVarsVisitor();
            sequentFormula.formula().execPostOrder(bvv);
            if (bvv.getBoundVariables().contains(v)) {
                return true;
            }
        }
        return false;
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
        for (final SequentFormula sf : this) {
            result.addAll(getLabelsForTermRecursively(sf.formula()));
        }
        return result;
    }

    /**
     * used to check whether this sequent contains a given sequent formula.
     *
     * @param form the given formula
     * @return true if this sequent contains the given formula
     */
    public boolean contains(SequentFormula form) {
        return antecedent().contains(form) || succedent().contains(form);
    }

    /**
     * Returns a list containing every {@link SequentFormula} in this sequent.
     *
     * @return a list containing every {@link SequentFormula} in this sequent.
     */
    public ImmutableList<SequentFormula> asList() {
        return antecedent().asList().append(succedent().asList());
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
