/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.calculus;

import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.sequent.SequentKit;
import org.key_project.util.collection.ImmutableList;

public class JavaDLSequentKit extends SequentKit {
    protected static JavaDLSequentKit INSTANCE = new JavaDLSequentKit();

    public synchronized static JavaDLSequentKit getInstance() {
        if (INSTANCE == null) {
            throw new IllegalStateException("SequentKit not initialized");
        }
        return INSTANCE;
    }

    protected JavaDLSequentKit() {
        super();
    }

    @Override
    public Semisequent getEmptySemisequent() {
        return de.uka.ilkd.key.proof.calculus.Semisequent.EMPTY_SEMISEQUENT;
    }

    @Override
    public Sequent getEmptySequent() {
        return de.uka.ilkd.key.proof.calculus.Sequent.EMPTY_SEQUENT;
    }

    /**
     * creates a new Sequent with empty succedent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public static org.key_project.prover.sequent.Sequent createAnteSequent(
            ImmutableList<SequentFormula> ante) {
        return getInstance().newAntecedent(ante);
    }

    /**
     * creates a new Sequent with empty antecedent
     *
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public static org.key_project.prover.sequent.Sequent createSuccSequent(
            ImmutableList<SequentFormula> succ) {
        return getInstance().newSuccedent(succ);
    }

    /**
     * creates a new Sequent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public static org.key_project.prover.sequent.Sequent createSequent(
            ImmutableList<SequentFormula> ante,
            ImmutableList<SequentFormula> succ) {
        return getInstance().newSequent(ante, succ);
    }

    @Override
    protected Semisequent createSemisequent(ImmutableList<SequentFormula> ante) {
        return ante.isEmpty() ? de.uka.ilkd.key.proof.calculus.Semisequent.EMPTY_SEMISEQUENT
                : new de.uka.ilkd.key.proof.calculus.Semisequent(ante);
    }

    /**
     * creates a new Sequent
     *
     * @param antecedent the Semisequent that plays the antecedent part
     * @param succedent the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    @Override
    protected Sequent createSequent(Semisequent antecedent, Semisequent succedent) {
        return new de.uka.ilkd.key.proof.calculus.Sequent(antecedent, succedent);
    }

    /** the empty semisequent (using singleton pattern) */
    public static Semisequent emptySemisequent() {
        return getInstance().getEmptySemisequent();
    }

}
