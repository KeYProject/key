/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

public class Sequent extends org.key_project.ncore.sequent.Sequent {
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
    public Semisequent antecedent() {
        return (Semisequent) super.antecedent();
    }

    @Override
    public Semisequent succedent() {
        return (Semisequent) super.succedent();
    }

    /**
     * replaces the antecedent ({@code antec} is true) of this sequent by the given
     * {@link Semisequent} similar for the succedent if {@code antec} is false.
     *
     * @param antec if the antecedent or succedent shall be replaced
     * @param semiSeq the {@link Semisequent} to use
     * @return the resulting sequent
     */
    @Override
    protected Sequent composeSequent(boolean antec,
            org.key_project.ncore.sequent.Semisequent semiSeq) {
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

        var semiSequent = (Semisequent) semiSeq;
        return new Sequent(antec ? semiSequent : antecedent(), antec ? succedent() : semiSequent);
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
        public @NonNull Iterator<org.key_project.ncore.sequent.SequentFormula> iterator() {
            return ImmutableSLList.<org.key_project.ncore.sequent.SequentFormula>nil().iterator();
        }
    }
}
