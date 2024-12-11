/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import static org.key_project.rusty.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

public class Semisequent extends org.key_project.prover.sequent.Semisequent {
    /** the empty semisequent (using singleton pattern) */
    public static final Semisequent EMPTY_SEMISEQUENT = new Empty();

    /** used by inner class Empty */
    private Semisequent() {
        super();
    }

    /**
     * Create a new Semisequent from an ordered collection of formulas.
     * The provided list must be redundancy free, i.e., the created sequent must be exactly
     * the same as when creating the sequent by subsequently inserting all formulas
     *
     * @param seqList list of sequent formulas
     */
    public Semisequent(ImmutableList<SequentFormula> seqList) {
        super(seqList);
    }

    /**
     * creates a new Semisequent with the Semisequent elements in seqList
     */
    public Semisequent(SequentFormula seqFormula) {
        super(ImmutableSLList.<SequentFormula>nil().append(seqFormula));
    }

    @Override
    protected boolean equalsModRenaming(SequentFormula sf1, SequentFormula sf2) {
        return RENAMING_TERM_PROPERTY.equalsModThisProperty(sf1.formula(), sf2.formula());
    }

    @Override
    protected SemisequentChangeInfo createSemisequentChangeInfo(
            ImmutableList<SequentFormula> seqList) {
        return new org.key_project.rusty.logic.SemisequentChangeInfo(seqList);
    }

    // inner class used to represent an empty semisequent
    private static class Empty extends Semisequent {

        private Empty() {
            super();
        }
    }
}
