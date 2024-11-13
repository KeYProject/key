/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.logic.Name;
import org.key_project.ncore.sequent.PosInOccurrence;
import org.key_project.ncore.sequent.SequentChangeInfo;
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
public class Sequent extends org.key_project.ncore.sequent.Sequent<SequentFormula> {
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
        super(Semisequent.EMPTY_SEMISEQUENT);
    }

    /** creates new Sequent with antecedence and succedence */
    private Sequent(Semisequent antecedent, Semisequent succedent) {
        super(antecedent, succedent);
    }

    @Override
    public final Semisequent antecedent() {
        return (Semisequent) super.antecedent();
    }

    @Override
    public Semisequent succedent() {
        return (Semisequent) super.succedent();
    }

    @Override
    public SequentChangeInfo<SequentFormula> addFormula(SequentFormula cf, PosInOccurrence p) {
        return super.addFormula(cf, p);
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
            org.key_project.ncore.sequent.Semisequent<SequentFormula> p_semiSeq) {
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

        return new Sequent(antec ? semiSeq : antecedent(), antec ? succedent() : semiSeq);
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
