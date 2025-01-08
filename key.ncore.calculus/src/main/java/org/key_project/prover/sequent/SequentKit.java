/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

import org.key_project.util.collection.ImmutableList;

public abstract class SequentKit {

    /**
     * Create a new Semisequent from an ordered collection of formulas (possibly empty).
     * The provided collection must be redundancy free, i.e., the created sequent must be exactly
     * the same as when creating the sequent by subsequently inserting all formulas.
     *
     * @param seqList list of sequent formulas
     */
    // public static Semisequent create(ImmutableList<SequentFormula> seqList, Property<? super
    // Term> redundanceProperty) {
    // if (seqList.isEmpty()) {
    // return EMPTY_SEMISEQUENT;
    // }
    // return new Semisequent(seqList, redundanceProperty);
    // }

    // INSTANCE FIELDS and METHODS

    protected SequentKit() {
    }

    public abstract Semisequent getEmptySemisequent();

    public abstract Sequent getEmptySequent();

    /**
     * creates a new Sequent with empty succedent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    protected Sequent newAntecedent(Semisequent ante) {
        if (ante.isEmpty()) {
            return getEmptySequent();
        }
        return createSequent(ante, getEmptySemisequent());
    }

    /**
     * creates a new Sequent with empty succedent
     *
     * @param ante the list of sequent formulas constituting the antecedent (must be redundant-free)
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public Sequent newAntecedent(ImmutableList<SequentFormula> ante) {
        return newAntecedent(
            ante.isEmpty() ? getEmptySemisequent() : createSemisequent(ante));
    }

    abstract protected Semisequent createSemisequent(ImmutableList<SequentFormula> ante);

    /**
     * creates a new Sequent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    protected Sequent newSequent(Semisequent ante, Semisequent succ) {
        if (ante.isEmpty() && succ.isEmpty()) {
            return getEmptySequent();
        }
        return createSequent(ante, succ);
    }

    /**
     * creates a new Sequent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    abstract protected Sequent createSequent(Semisequent ante, Semisequent succ);

    /**
     * creates a new Sequent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public Sequent newSequent(ImmutableList<SequentFormula> ante,
            ImmutableList<SequentFormula> succ) {
        return newSequent(
            ante.isEmpty() ? getEmptySemisequent() : createSemisequent(ante),
            succ.isEmpty() ? getEmptySemisequent() : createSemisequent(succ));
    }

    /**
     * creates a new Sequent with empty antecedent
     *
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    protected Sequent newSuccedent(Semisequent succ) {
        if (succ.isEmpty()) {
            return getEmptySequent();
        }
        return createSequent(getEmptySemisequent(), succ);
    }

    public Sequent newSuccedent(ImmutableList<SequentFormula> succ) {
        return newSuccedent(
            succ.isEmpty() ? getEmptySemisequent() : createSemisequent(succ));
    }
}
