/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.equality.RenamingTermProperty;

import org.key_project.logic.Property;
import org.key_project.logic.Term;
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
        super(new Semisequent.Empty(RenamingTermProperty.RENAMING_TERM_PROPERTY));
    }


    /**
     * creates a new Sequent with empty succedent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public static Sequent createAnteSequent(Semisequent ante) {
        return getInstance().newAntecedent(ante);
    }

    /**
     * creates a new Sequent with empty succedent
     *
     * @param ante the Semisequent that plays the antecedent part
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
    public static Sequent createSuccSequent(Semisequent succ) {
        return getInstance().newSuccedent(succ);
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

    /**
     * creates a new Sequent
     *
     * @param ante the Semisequent that plays the antecedent part
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are same as
     *         EMPTY_SEMISEQUENT
     */
    public static Sequent createSequent(Semisequent ante,
            Semisequent succ) {
        return getInstance().newSequent(ante, succ);
    }

    public static Sequent createSequent(ImmutableList<SequentFormula> ante,
            ImmutableList<SequentFormula> succ) {
        return getInstance().newSequent(ante, succ);
    }

    public static Sequent getEmptySequent() {
        return getInstance().emptySequent();
    }

    /** the empty semisequent (using singleton pattern) */
    public static Semisequent emptySemisequent() {
        return getInstance().getEmptySemisequent();
    }

    @Override
    protected Property<Term> getRedundancyProperty() {
        return RenamingTermProperty.RENAMING_TERM_PROPERTY;
    }

}
