/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

import static org.key_project.rusty.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

public class Semisequent implements Iterable<SequentFormula> {
    /** the empty semisequent (using singleton pattern) */
    public static final Semisequent EMPTY_SEMISEQUENT = new Empty();
    /** list with the {@link SequentFormula}s of the Semisequent */
    private final ImmutableList<SequentFormula> seqList;

    /** used by inner class Empty */
    private Semisequent() {
        seqList = ImmutableSLList.nil();
    }

    /**
     * Create a new Semisequent from an ordered collection of formulas.
     * The provided list must be redundancy free, i.e., the created sequent must be exactly
     * the same as when creating the sequent by subsequently inserting all formulas
     *
     * @param seqList list of sequent formulas
     */
    public Semisequent(ImmutableList<SequentFormula> seqList) {
        assert !seqList.isEmpty();
        this.seqList = seqList;
    }

    /**
     * creates a new Semisequent with the Semisequent elements in seqList
     */
    public Semisequent(SequentFormula seqFormula) {
        assert seqFormula != null;
        this.seqList = ImmutableSLList.<SequentFormula>nil().append(seqFormula);
    }

    /**
     * inserts an element at a specified index performing redundancy checks, this may result in
     * returning same semisequent if inserting would create redundancies
     *
     * @param idx int encoding the place the element has to be put
     * @param sequentFormula {@link SequentFormula} to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insert(int idx, SequentFormula sequentFormula) {
        return removeRedundance(idx, sequentFormula);
    }

    /**
     * inserts element at index 0 performing redundancy checks, this may result in returning same
     * semisequent if inserting would create redundancies
     *
     * @param sequentFormula SequentFormula to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insertFirst(SequentFormula sequentFormula) {
        return insert(0, sequentFormula);
    }

    /**
     * is this a semisequent that contains no formulas
     *
     * @return true if the semisequent contains no formulas
     */
    public boolean isEmpty() {
        return seqList.isEmpty();
    }

    /**
     * inserts new SequentFormula at index idx and removes duplicates, perform simplifications etc.
     *
     * @param fci null if the formula to be added is new, otherwise an object telling which formula
     *        is replaced with the new formula <code>sequentFormula</code>, and what are the
     *        differences between the two formulas
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    private SemisequentChangeInfo insertAndRemoveRedundancyHelper(int idx,
            SequentFormula sequentFormula, SemisequentChangeInfo semiCI, FormulaChangeInfo fci) {

        // Search for equivalent formulas and weakest constraint
        ImmutableList<SequentFormula> searchList = semiCI.getFormulaList();
        final SequentFormula[] newSeqList = new SequentFormula[searchList.size()];
        SequentFormula cf;
        int pos = -1;

        while (!searchList.isEmpty()) {
            ++pos;
            cf = searchList.head();
            searchList = searchList.tail();

            if (sequentFormula != null
                    && RENAMING_TERM_PROPERTY.equalsModThisProperty(cf.formula(),
                        sequentFormula.formula())) {
                semiCI.rejectedFormula(sequentFormula);
                return semiCI; // semisequent already contains formula

            }
            newSeqList[pos] = cf;
        }


        // compose resulting formula list
        if (fci == null) {
            semiCI.addedFormula(idx, sequentFormula);
        } else {
            semiCI.modifiedFormula(idx, fci);
        }

        final ImmutableList<SequentFormula> orig = semiCI.getFormulaList();
        pos = Math.min(idx, orig.size());

        searchList = semiCI.getFormulaList().take(pos).prepend(sequentFormula);

        while (pos > 0) {
            --pos;
            searchList = searchList.prepend(newSeqList[pos]);
        }

        // add new formula list to result object
        semiCI.setFormulaList(searchList);

        return semiCI;
    }

    /**
     * . inserts new SequentFormula at index {@code idx} and removes duplicates, perform
     * simplifications etc.
     *
     * @param sequentFormula the SequentFormula to be inserted at position idx
     * @param idx an int that means insert sequentFormula at the idx-th position in the semisequent
     * @return new Semisequent with sequentFormula at index idx and removed redundancies
     */
    private SemisequentChangeInfo removeRedundance(int idx, SequentFormula sequentFormula) {
        return insertAndRemoveRedundancyHelper(idx, sequentFormula,
            new SemisequentChangeInfo(seqList), null);
    }

    /**
     * gets the element at a specific index
     *
     * @param idx int representing the index of the element we want to have
     * @return {@link SequentFormula} found at index idx
     * @throws IndexOutOfBoundsException if idx is negative or greater or equal to
     *         {@link Sequent#size()}
     */
    public SequentFormula get(int idx) {
        if (idx < 0 || idx >= seqList.size()) {
            throw new IndexOutOfBoundsException();
        }
        return seqList.take(idx).head();
    }

    /** @return the first {@link SequentFormula} of this Semisequent */
    public SequentFormula getFirst() {
        return seqList.head();
    }

    /**
     * returns iterator about the elements of the sequent
     *
     * @return Iterator<SequentFormula>
     */
    @Override
    public @NonNull Iterator<SequentFormula> iterator() {
        return seqList.iterator();
    }

    public ImmutableList<SequentFormula> asList() {
        return seqList;
    }

    /** @return int counting the elements of this semisequent */
    public int size() {
        return seqList.size();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Semisequent)) {
            return false;
        }
        return seqList.equals(((Semisequent) o).seqList);
    }

    /** @return String representation of this Semisequent */
    @Override
    public String toString() {
        return seqList.toString();
    }

    // inner class used to represent an empty semisequent
    private static class Empty extends Semisequent {

        private Empty() {
            super();
        }
    }
}
