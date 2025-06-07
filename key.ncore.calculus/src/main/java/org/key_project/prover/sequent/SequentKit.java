/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

import org.key_project.util.collection.ImmutableList;

public abstract class SequentKit {

    // INSTANCE FIELDS and METHODS

    protected SequentKit() {
    }

    /**
     * Returns a semisequent with no formulas.
     * <p>
     * This factory method is implemented by inheriting classes. It is encouraged but not enforced
     * to use a singleton pattern for empty semisequents.
     * </p>
     *
     * @return the empty semisequent
     */
    public abstract Semisequent getEmptySemisequent();

    /**
     * Returns a sequent with no formulas.
     * <p>
     * This factory method is implemented by inheriting classes. It is encouraged but not enforced
     * to use a singleton pattern for empty sequents.
     * </p>
     *
     * @return the empty sequent
     */
    public abstract Sequent getEmptySequent();

    /**
     * creates a new {@link Sequent} with empty succedent
     *
     * @param antecedent the {@link Semisequent} that will become the antecedent
     * @return the new sequent or the {@link #getEmptySequent()}
     *         if {@code antecedent} is empty
     */
    protected Sequent newAntecedent(Semisequent antecedent) {
        if (antecedent.isEmpty()) {
            return getEmptySequent();
        }
        return createSequent(antecedent, getEmptySemisequent());
    }

    /**
     * creates a new {@link Sequent} with empty succedent
     *
     * @param antecedent the {@link ImmutableList} of {@link SequentFormula}s constituting the
     *        antecedent
     * @return the new sequent or the {@link #getEmptySequent()} if {@code antecedent} is the empty
     *         list
     */
    public Sequent newAntecedent(ImmutableList<SequentFormula> antecedent) {
        return newAntecedent(
            antecedent.isEmpty() ? getEmptySemisequent() : createSemisequent(antecedent));
    }

    abstract protected Semisequent createSemisequent(ImmutableList<SequentFormula> ante);

    /**
     * creates a new {@link Sequent}
     *
     * @param antecedent the {@link Semisequent} that will become the antecedent
     * @param succedent the {@link Semisequent} that will become the succedent
     *
     * @return the new sequent or the {@link #getEmptySequent()} if both antecedent and succedent
     *         are empty
     */
    protected Sequent newSequent(Semisequent antecedent, Semisequent succedent) {
        if (antecedent.isEmpty() && succedent.isEmpty()) {
            return getEmptySequent();
        }
        return createSequent(antecedent, succedent);
    }

    /**
     * creates a new {@link Sequent}
     *
     * @param antecedent the {@link Semisequent} that will become the antecedent
     * @param succedent the {@link Semisequent} that will become the succedent
     *
     * @return the new sequent or the {@link #getEmptySequent()} if both antecedent
     *         and succedent are empty
     */
    abstract protected Sequent createSequent(Semisequent antecedent, Semisequent succedent);

    /**
     * creates a new {@link Sequent}
     *
     * @param antecedent the {@link ImmutableList} of {@link SequentFormula}s constituting the
     *        antecedent
     * @param succedent the {@link ImmutableList} of {@link SequentFormula}s constituting the
     *        succedent
     *
     * @return the new sequent or the {@link #getEmptySequent()} if both antecedent
     *         and succedent are empty
     */
    public Sequent newSequent(ImmutableList<SequentFormula> antecedent,
            ImmutableList<SequentFormula> succedent) {
        return newSequent(
            antecedent.isEmpty() ? getEmptySemisequent() : createSemisequent(antecedent),
            succedent.isEmpty() ? getEmptySemisequent() : createSemisequent(succedent));
    }

    /**
     * creates a new {@link Sequent} with empty antecedent
     *
     * @param succedent the {@link Semisequent} that plays the succedent part
     *
     * @return the new sequent or the {@link #getEmptySequent()} if the succedent is empty
     */
    protected Sequent newSuccedent(Semisequent succedent) {
        if (succedent.isEmpty()) {
            return getEmptySequent();
        }
        return createSequent(getEmptySemisequent(), succedent);
    }

    /**
     * creates a new {@link Sequent} with an empty antecedent
     *
     * @param succedent the {@link ImmutableList} of {@link SequentFormula}s constituting the
     *        succedent
     * @return the new sequent or the {@link #getEmptySequent()} if {@code succedent} is the empty
     *         list
     */
    public Sequent newSuccedent(ImmutableList<SequentFormula> succedent) {
        return newSuccedent(
            succedent.isEmpty() ? getEmptySemisequent() : createSemisequent(succedent));
    }
}
