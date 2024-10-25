/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Collection;

import org.key_project.ncore.sequent.SemisequentChangeInfo;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;


/**
 * This class represents the succedent or antecendent part of a sequent. It is more or less a list
 * without duplicates and subsumed formulas. This is ensured using method removeRedundancy. In
 * future versions it can be enhanced to do other simplifications. A sequent and so a semisequent
 * has to be immutable.
 */
public class Semisequent extends org.key_project.ncore.sequent.Semisequent {

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
    public Semisequent(ImmutableList<org.key_project.ncore.sequent.SequentFormula> seqList) {
        super(seqList);
    }

    /**
     * Create a new Semisequent from an ordered collection of formulas.
     * The provided collection must be redundancy free, i.e., the created sequent must be exactly
     * the same as when creating the sequent by subsequently inserting all formulas
     *
     * @param seqList list of sequent formulas
     */
    public Semisequent(Collection<SequentFormula> seqList) {
        this(ImmutableList.fromList(seqList));
    }


    @Override
    protected boolean equalsModRenaming(org.key_project.ncore.sequent.SequentFormula sf1,
                                        org.key_project.ncore.sequent.SequentFormula sf2) {
        return RENAMING_TERM_PROPERTY.equalsModThisProperty(sf1.formula(), sf2.formula());
    }

    @Override
    protected SemisequentChangeInfo createSemisequentChangeInfo(ImmutableList<org.key_project.ncore.sequent.SequentFormula> seqList) {
        return null;
    }


    /**
     * Create a new Semisequent from an ordered collection of formulas (possibly empty).
     * The provided collection must be redundancy free, i.e., the created sequent must be exactly
     * the same as when creating the
     * sequent by subsequently inserting all formulas.
     *
     * @param seqList list of sequent formulas
     */
    public static Semisequent create(Collection<SequentFormula> seqList) {
        if (seqList.isEmpty()) {
            return EMPTY_SEMISEQUENT;
        }
        return new Semisequent(seqList);
    }


    /**
     * creates a new Semisequent with the Semisequent elements in seqList
     */
    public Semisequent(SequentFormula seqFormula) {
        super(ImmutableSLList.<org.key_project.ncore.sequent.SequentFormula>nil().append(seqFormula));
    }

    // inner class used to represent an empty semisequent
    private static class Empty extends Semisequent {
        private Empty() {
            super();
        }
    }
}
