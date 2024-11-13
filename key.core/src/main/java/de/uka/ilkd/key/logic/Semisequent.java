/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Collection;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;


/**
 * This class represents the succedent or antecendent part of a sequent. It is more or less a list
 * without duplicates and subsumed formulas. This is ensured using method removeRedundancy. In
 * future versions it can be enhanced to do other simplifications. A sequent and so a semisequent
 * has to be immutable.
 */
public class Semisequent extends org.key_project.ncore.sequent.Semisequent<SequentFormula> {
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
     * Create a new Semisequent from an ordered collection of formulas.
     * The provided collection must be redundancy free, i.e., the created sequent must be exactly
     * the same as when creating the sequent by subsequently inserting all formulas
     *
     * @param seqList list of sequent formulas
     */
    public Semisequent(Collection<SequentFormula> seqList) {
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
        return RENAMING_TERM_PROPERTY.equalsModThisProperty(sf1.formula(),
            sf2.formula());
    }

    @Override
    protected SemisequentChangeInfo createSemisequentChangeInfo(
            ImmutableList<SequentFormula> seqList) {
        return new SemisequentChangeInfo(seqList);
    }

    @Override
    public SemisequentChangeInfo insert(int idx, ImmutableList<SequentFormula> insertionList) {
        return (SemisequentChangeInfo) super.insert(idx, insertionList);
    }

    @Override
    public SemisequentChangeInfo insert(int idx, SequentFormula sequentFormula) {
        return (SemisequentChangeInfo) super.insert(idx, sequentFormula);
    }

    @Override
    public SemisequentChangeInfo insertLast(ImmutableList<SequentFormula> insertions) {
        return (SemisequentChangeInfo) super.insertLast(insertions);
    }

    @Override
    public SemisequentChangeInfo insertLast(SequentFormula sequentFormula) {
        return (SemisequentChangeInfo) super.insertLast(sequentFormula);
    }

    @Override
    public SemisequentChangeInfo replace(int idx, SequentFormula sequentFormula) {
        return (SemisequentChangeInfo) super.replace(idx, sequentFormula);
    }

    @Override
    public SemisequentChangeInfo replace(int idx, ImmutableList<SequentFormula> replacements) {
        return (SemisequentChangeInfo) super.replace(idx, replacements);
    }

    @Override
    public SemisequentChangeInfo remove(int idx) {
        return (SemisequentChangeInfo) super.remove(idx);
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


    // inner class used to represent an empty semisequent
    private static class Empty extends Semisequent {
        private Empty() {
            super();
        }
    }
}
