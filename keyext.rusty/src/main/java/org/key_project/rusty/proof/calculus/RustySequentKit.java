/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.calculus;

import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.sequent.SequentKit;
import org.key_project.util.collection.ImmutableList;

public class RustySequentKit extends SequentKit {

    protected static RustySequentKit INSTANCE = new RustySequentKit();

    public static RustySequentKit getInstance() {
        if (INSTANCE == null) {
            throw new IllegalStateException("SequentKit not initialized");
        }
        return INSTANCE;
    }

    public static Sequent createSequent(ImmutableList<SequentFormula> ante,
            ImmutableList<SequentFormula> succ) {
        return getInstance().newSequent(ante, succ);
    }

    /**
     * creates a new Sequent with empty succedent
     *
     * @param ante list of redundant-free formulas that plays the antecedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public static Sequent createAnteSequent(ImmutableList<SequentFormula> ante) {
        return getInstance().newAntecedent(ante);
    }

    /**
     * creates a new Sequent with empty antecedent
     *
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public static Sequent createSuccSequent(ImmutableList<SequentFormula> succ) {
        return getInstance().newSuccedent(succ);
    }

    protected RustySequentKit() {
        super();
    }

    @Override
    public Semisequent getEmptySemisequent() {
        return org.key_project.rusty.proof.calculus.Semisequent.EMPTY_SEMISEQUENT;
    }


    @Override
    public Sequent getEmptySequent() {
        return org.key_project.rusty.proof.calculus.Sequent.EMPTY_SEQUENT;
    }

    /**
     * creates a new Sequent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    @Override
    protected Sequent createSequent(Semisequent ante, Semisequent succ) {
        if (ante.isEmpty() && succ.isEmpty()) {
            return getEmptySequent();
        }
        return new org.key_project.rusty.proof.calculus.Sequent(ante, succ);
    }

    @Override
    protected Semisequent createSemisequent(ImmutableList<SequentFormula> sequentFormulas) {
        return sequentFormulas.isEmpty()
                ? org.key_project.rusty.proof.calculus.Semisequent.EMPTY_SEMISEQUENT
                : new org.key_project.rusty.proof.calculus.Semisequent(sequentFormulas);
    }

}
