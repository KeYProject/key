/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.sequent;

import java.util.Collection;
import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

/**
 * Subclasses must add static EMPTY_SEMISEQUENT
 */
public abstract class Semisequent<SF extends SequentFormula> implements Iterable<SF> {
    /** list with the {@link SequentFormula}s of the Semisequent */
    private final ImmutableList<SF> seqList;

    /** used by inner class Empty */
    protected Semisequent() {
        seqList = ImmutableSLList.nil();
    }

    /**
     * Create a new Semisequent from an ordered collection of formulas.
     * The provided list must be redundancy free, i.e., the created sequent must be exactly
     * the same as when creating the sequent by subsequently inserting all formulas
     *
     * @param seqList list of sequent formulas
     */
    public Semisequent(ImmutableList<SF> seqList) {
        assert !seqList.isEmpty();
        this.seqList = seqList;
    }

    /**
     * Create a new Semisequent from an ordered collection of formulas.
     * The provided collection must be redundancy free, i.e., the created sequent must be exactly
     * the same as when creating the sequent by subsequently inserting all formulas
     *
     * @param seqList list of sequent formulas
     */
    public Semisequent(Collection<SF> seqList) {
        this(ImmutableList.fromList(seqList));
    }

    /**
     * creates a new Semisequent with the Semisequent elements in seqList
     */
    public Semisequent(SF seqFormula) {
        assert seqFormula != null;
        this.seqList = ImmutableSLList.<SF>nil().append(seqFormula);
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
    public SemisequentChangeInfo<SF> insert(int idx, SF sequentFormula) {
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
    public SemisequentChangeInfo<SF> insertFirst(SF sequentFormula) {
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

    protected abstract boolean equalsModRenaming(SF sf1, SF sf2);

    /**
     * inserts new SequentFormula at index idx and removes duplicates, perform simplifications etc.
     *
     * @param fci null if the formula to be added is new, otherwise an object telling which formula
     *        is replaced with the new formula <code>sequentFormula</code>, and what are the
     *        differences between the two formulas
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    private SemisequentChangeInfo<SF> insertAndRemoveRedundancyHelper(int idx,
            SF sequentFormula, SemisequentChangeInfo<SF> semiCI, FormulaChangeInfo<SF> fci) {
        // Search for equivalent formulas and weakest constraint
        ImmutableList<SF> searchList = semiCI.getFormulaList();
        final var newSeqList = new SequentFormula[searchList.size()];
        SF sf;
        int pos = -1;

        while (!searchList.isEmpty()) {
            ++pos;
            sf = searchList.head();
            searchList = searchList.tail();

            if (sequentFormula != null
                    && equalsModRenaming(sf, sequentFormula)) {
                semiCI.rejectedFormula(sequentFormula);
                return semiCI; // semisequent already contains formula

            }
            newSeqList[pos] = sf;
        }


        // compose resulting formula list
        if (fci == null) {
            semiCI.addedFormula(idx, sequentFormula);
        } else {
            semiCI.modifiedFormula(idx, fci);
        }

        final var orig = semiCI.getFormulaList();
        pos = Math.min(idx, orig.size());

        searchList = semiCI.getFormulaList().take(pos).prepend(sequentFormula);

        while (pos > 0) {
            --pos;
            searchList = searchList.prepend((SF) newSeqList[pos]);
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
    private SemisequentChangeInfo<SF> removeRedundance(int idx, SF sequentFormula) {
        return insertAndRemoveRedundancyHelper(idx, sequentFormula,
            createSemisequentChangeInfo(seqList), null);
    }

    protected abstract SemisequentChangeInfo<SF> createSemisequentChangeInfo(
            ImmutableList<SF> seqList);

    /**
     * . inserts new ConstrainedFormulas starting at index idx and removes duplicates, perform
     * simplifications etc.
     *
     * @param sequentFormula the IList<SequentFormula> to be inserted at position idx
     * @param idx an int that means insert sequentFormula at the idx-th position in the semisequent
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    private SemisequentChangeInfo<SF> removeRedundance(int idx,
            ImmutableList<SF> sequentFormula) {
        return insertAndRemoveRedundancy(idx, sequentFormula, createSemisequentChangeInfo(seqList));
    }

    /**
     * . inserts new ConstrainedFormulas starting at index idx and removes duplicates, perform
     * simplifications etc.
     *
     * @param sequentFormulasToBeInserted the {@link ImmutableList<SF>} to be inserted
     *        at position idx
     * @param idx an int that means insert sequentFormula at the idx-th position in the semisequent
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    private SemisequentChangeInfo<SF> insertAndRemoveRedundancy(int idx,
            ImmutableList<SF> sequentFormulasToBeInserted,
            SemisequentChangeInfo<SF> sci) {

        int pos = idx;
        ImmutableList<SF> oldFormulas = sci.getFormulaList();

        while (!sequentFormulasToBeInserted.isEmpty()) {
            final SF aSequentFormula = sequentFormulasToBeInserted.head();
            sequentFormulasToBeInserted = sequentFormulasToBeInserted.tail();

            sci = insertAndRemoveRedundancyHelper(pos, aSequentFormula, sci, null);

            if (sci.getFormulaList() != oldFormulas) {
                pos = sci.getIndex() + 1;
                oldFormulas = sci.getFormulaList();
            }
        }
        return sci;
    }

    /**
     * gets the element at a specific index
     *
     * @param idx int representing the index of the element we want to have
     * @return {@link SequentFormula} found at index idx
     * @throws IndexOutOfBoundsException if idx is negative or greater or equal to
     *         {@link Sequent#size()}
     */
    public SF get(int idx) {
        if (idx < 0 || idx >= seqList.size()) {
            throw new IndexOutOfBoundsException();
        }
        return seqList.take(idx).head();
    }

    /** @return the first {@link SequentFormula} of this Semisequent */
    public SF getFirst() {
        return seqList.head();
    }

    /**
     * returns iterator about the elements of the sequent
     *
     * @return Iterator<SequentFormula>
     */
    @Override
    public @NonNull Iterator<SF> iterator() {
        return seqList.iterator();
    }

    public ImmutableList<SF> asList() {
        return seqList;
    }

    /** @return int counting the elements of this semisequent */
    public int size() {
        return seqList.size();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Semisequent<?> s)) {
            return false;
        }
        return seqList.equals(s.seqList);
    }

    /** @return String representation of this Semisequent */
    @Override
    public String toString() {
        return seqList.toString();
    }

    /**
     * inserts the elements of the list at the specified index performing redundancy checks
     *
     * @param idx int encoding the place where the insertion starts
     * @param insertionList IList<SequentFormula> to be inserted starting at idx
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo<SF> insert(int idx,
            ImmutableList<SF> insertionList) {
        return removeRedundance(idx, insertionList);
    }

    /**
     * inserts element at the end of the semisequent performing redundancy checks, this may result
     * in returning same semisequent if inserting would create redundancies
     *
     * @param sequentFormula {@link SequentFormula} to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo<SF> insertLast(SF sequentFormula) {
        return insert(size(), sequentFormula);
    }

    /**
     * returns the index of the given {@link SequentFormula} or {@code -1} if the sequent formula is
     * not found. Equality of sequent formulas is checked sing the identy check (i.e.,
     * <code>==</code>)
     *
     * @param sequentFormula the {@link SequentFormula} to look for
     * @return index of sequentFormula (-1 if not found)
     */
    public int indexOf(SF sequentFormula) {
        ImmutableList<SF> searchList = seqList;
        int index = 0;
        while (!searchList.isEmpty()) {
            if (searchList.head() == sequentFormula) {
                return index;
            }
            searchList = searchList.tail();
            index++;
        }
        return -1;
    }

    /**
     * inserts element at index 0 performing redundancy checks, this may result in returning same
     * semisequent if inserting would create redundancies
     *
     * @param insertions IList<SequentFormula> to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo<SF> insertFirst(ImmutableList<SF> insertions) {
        return insert(0, insertions);
    }

    /**
     * inserts the formulas of the list at the end of the semisequent performing redundancy checks,
     * this may result in returning same semisequent if inserting would create redundancies
     *
     * @param insertions the IList<SequentFormula> to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo<SF> insertLast(ImmutableList<SF> insertions) {
        return insert(size(), insertions);
    }

    /**
     * replaces the element at place idx with the first element of the given list and adds the rest
     * of the list to the semisequent behind the replaced formula
     *
     * @param pos the formula to be replaced
     * @param replacements the IList<SequentFormula> whose head replaces the element at index idx
     *        and the tail is added to the semisequent
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo<SF> replace(PosInOccurrence pos,
            ImmutableList<SF> replacements) {
        final int idx = indexOf((SF) pos.sequentFormula());
        return insertAndRemoveRedundancy(idx, replacements, remove(idx));
    }

    /**
     * removes an element
     *
     * @param idx int being the index of the element that has to be removed
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo<SF> remove(int idx) {
        ImmutableList<SF> newList = seqList;
        int index = 0;

        if (idx < 0 || idx >= size()) {
            return createSemisequentChangeInfo(seqList);
        }

        final SequentFormula[] temp = new SequentFormula[idx];

        while (index < idx) {// go to idx
            temp[index] = newList.head();
            newList = newList.tail();
            index++;
        }

        // remove the element that is at head of newList
        final SF removedFormula = newList.head();
        newList = newList.tail();

        for (int k = index - 1; k >= 0; k--) {
            newList = newList.prepend((SF) temp[k]);
        }

        // create change info object
        final SemisequentChangeInfo<SF> sci = createSemisequentChangeInfo(newList);
        sci.removedFormula(idx, removedFormula);

        return sci;
    }

    /**
     * replaces the element at place idx with sequentFormula
     *
     * @param pos the PosInOccurrence describing the position of and within the formula below which
     *        the formula differs from the new formula <code>sequentFormula</code>
     * @param sequentFormula the SequentFormula replacing the old element at index idx
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo<SF> replace(PosInOccurrence pos, SF sequentFormula) {
        final int idx = indexOf((SF) pos.sequentFormula());
        final FormulaChangeInfo<SF> fci = new FormulaChangeInfo<>(pos, sequentFormula);
        return insertAndRemoveRedundancyHelper(idx, sequentFormula, remove(idx), fci);
    }

    /**
     * replaces the element at place idx with sequentFormula
     *
     * @param idx an int specifying the index of the element that has to be replaced
     * @param sequentFormula the {@link SequentFormula} replacing the old element at index idx
     * @return semisequent change information object with new semisequent with sequentFormula at
     *         place idx
     */
    public SemisequentChangeInfo<SF> replace(int idx, SF sequentFormula) {
        return insertFirst(sequentFormula);
    }

    /**
     * checks if the {@link SequentFormula} occurs in this Semisequent (identity check)
     *
     * @param sequentFormula the {@link SequentFormula} to look for
     * @return true iff. sequentFormula has been found in this Semisequent
     */
    public boolean contains(SF sequentFormula) {
        return indexOf(sequentFormula) != -1;
    }
}
