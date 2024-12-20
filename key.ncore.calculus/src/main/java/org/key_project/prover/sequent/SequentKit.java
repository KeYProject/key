/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

import org.key_project.logic.Property;
import org.key_project.logic.Term;
import org.key_project.util.collection.ImmutableList;

public abstract class SequentKit {

    private final Sequent emptySequent;
    private final Semisequent emptySemisequent;

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

    protected SequentKit(Semisequent emptySemisequent) {
        this.emptySemisequent = emptySemisequent;
        this.emptySequent = new Sequent.NILSequent(emptySemisequent);
    }

    protected abstract Property<Term> getRedundancyProperty();

    public Semisequent getEmptySemisequent() {
        return emptySemisequent;
    }

    public Sequent emptySequent() {
        return emptySequent;
    }

    /**
     * creates a new Sequent with empty succedent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    protected Sequent newAntecedent(Semisequent ante) {
        if (ante.isEmpty()) {
            return emptySequent;
        }
        return new Sequent(ante, getEmptySemisequent());
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
            ante.isEmpty() ? emptySemisequent : new Semisequent(ante, getRedundancyProperty()));
    }

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
            return emptySequent;
        }
        return new Sequent(ante, succ);
    }

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
            ante.isEmpty() ? emptySemisequent : new Semisequent(ante, getRedundancyProperty()),
            succ.isEmpty() ? emptySemisequent : new Semisequent(succ, getRedundancyProperty()));
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
            return emptySequent;
        }
        return new Sequent(getEmptySemisequent(), succ);
    }

    public Sequent newSuccedent(ImmutableList<SequentFormula> succ) {
        return newSuccedent(
            succ.isEmpty() ? emptySemisequent : new Semisequent(succ, getRedundancyProperty()));
    }
}
