/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * This class represents the succedent or antecendent part of a sequent. It is more or less a list
 * without duplicates and subsumed formulas. This is ensured using method removeRedundancy. In
 * future versions it can be enhanced to do other simplifications. A sequent and so a semisequent
 * has to be immutable.
 */
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
     * creates a new Semisequent with the Semisequent elements in seqList; the provided list must be
     * redundancy free, i.e., the created sequent must be exactly the same as when creating the
     * sequent by subsequently inserting all formulas
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
     * inserts the elements of the list at the specified index performing redundancy checks
     *
     * @param idx int encoding the place where the insertion starts
     * @param insertionList IList<SequentFormula> to be inserted starting at idx
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insert(int idx, ImmutableList<SequentFormula> insertionList) {
        return removeRedundance(idx, insertionList);
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
     * inserts element at index 0 performing redundancy checks, this may result in returning same
     * semisequent if inserting would create redundancies
     *
     * @param insertions IList<SequentFormula> to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insertFirst(ImmutableList<SequentFormula> insertions) {
        return insert(0, insertions);
    }

    /**
     * inserts element at the end of the semisequent performing redundancy checks, this may result
     * in returning same semisequent if inserting would create redundancies
     *
     * @param sequentFormula {@link SequentFormula} to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insertLast(SequentFormula sequentFormula) {
        return insert(size(), sequentFormula);
    }

    /**
     * inserts the formulas of the list at the end of the semisequent performing redundancy checks,
     * this may result in returning same semisequent if inserting would create redundancies
     *
     * @param insertions the IList<SequentFormula> to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insertLast(ImmutableList<SequentFormula> insertions) {
        return insert(size(), insertions);
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
        assert idx >= 0;

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
                    && cf.formula().equalsModRenaming(sequentFormula.formula())) {
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
     * . inserts new ConstrainedFormulas starting at index idx and removes duplicates, perform
     * simplifications etc.
     *
     * @param sequentFormulasToBeInserted the {@link ImmutableList<SequentFormula>} to be inserted
     *        at position idx
     * @param idx an int that means insert sequentFormula at the idx-th position in the semisequent
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    private SemisequentChangeInfo insertAndRemoveRedundancy(int idx,
            ImmutableList<SequentFormula> sequentFormulasToBeInserted, SemisequentChangeInfo sci) {

        int pos = idx;
        ImmutableList<SequentFormula> oldFormulas = sci.getFormulaList();

        while (!sequentFormulasToBeInserted.isEmpty()) {
            final SequentFormula aSequentFormula = sequentFormulasToBeInserted.head();
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
     * . inserts new ConstrainedFormulas starting at index idx and removes duplicates, perform
     * simplifications etc.
     *
     * @param sequentFormula the IList<SequentFormula> to be inserted at position idx
     * @param idx an int that means insert sequentFormula at the idx-th position in the semisequent
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    private SemisequentChangeInfo removeRedundance(int idx,
            ImmutableList<SequentFormula> sequentFormula) {
        return insertAndRemoveRedundancy(idx, sequentFormula, new SemisequentChangeInfo(seqList));
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
     * replaces the element at place idx with sequentFormula
     *
     * @param pos the PosInOccurrence describing the position of and within the formula below which
     *        the formula differs from the new formula <code>sequentFormula</code>
     * @param sequentFormula the SequentFormula replacing the old element at index idx
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo replace(PosInOccurrence pos, SequentFormula sequentFormula) {
        final int idx = indexOf(pos.sequentFormula());
        assert idx >= 0;
        final FormulaChangeInfo fci = new FormulaChangeInfo(pos, sequentFormula);
        return insertAndRemoveRedundancyHelper(idx, sequentFormula, remove(idx), fci);
    }

    /**
     * replaces the <tt>idx</tt>-th formula by <tt>sequentFormula</tt>
     *
     * @param idx the int with the position of the formula to be replaced
     * @param sequentFormula the SequentFormula replacing the formula at the given position
     * @return a SemisequentChangeInfo containing the new sequent and a diff to the old one
     */
    public SemisequentChangeInfo replace(int idx, SequentFormula sequentFormula) {
        return insertAndRemoveRedundancyHelper(idx, sequentFormula, remove(idx), null);
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
    public SemisequentChangeInfo replace(PosInOccurrence pos,
            ImmutableList<SequentFormula> replacements) {
        final int idx = indexOf(pos.sequentFormula());
        return insertAndRemoveRedundancy(idx, replacements, remove(idx));
    }

    /**
     * replaces the formula at position {@code idx} by the given list of formulas
     *
     * @param idx the position
     * @param replacements the new formulas
     * @return change information including the resulting semisequent after the replacement
     */
    public SemisequentChangeInfo replace(int idx, ImmutableList<SequentFormula> replacements) {
        return insertAndRemoveRedundancy(idx, replacements, remove(idx));
    }

    /** @return int counting the elements of this semisequent */
    public int size() {
        return seqList.size();
    }


    /**
     * removes an element
     *
     * @param idx int being the index of the element that has to be removed
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo remove(int idx) {

        ImmutableList<SequentFormula> newList = seqList;
        int index = 0;

        if (idx < 0 || idx >= size()) {
            return new SemisequentChangeInfo(seqList);
        }

        final SequentFormula[] temp = new SequentFormula[idx];

        while (index < idx) {// go to idx
            temp[index] = newList.head();
            newList = newList.tail();
            index++;
        }

        // remove the element that is at head of newList
        final SequentFormula removedFormula = newList.head();
        newList = newList.tail();

        for (int k = index - 1; k >= 0; k--) {
            newList = newList.prepend(temp[k]);
        }

        // create change info object
        final SemisequentChangeInfo sci = new SemisequentChangeInfo(newList);
        sci.removedFormula(idx, removedFormula);

        return sci;
    }

    /**
     * returns the index of the given {@link SequentFormula} or {@code -1} if the sequent formula is
     * not found. Equality of sequent formulas is checked sing the identy check (i.e.,{@link ==})
     *
     * @param sequentFormula the {@link SequentFormula} to look for
     * @return index of sequentFormula (-1 if not found)
     */
    public int indexOf(SequentFormula sequentFormula) {
        ImmutableList<SequentFormula> searchList = seqList;
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
     * checks if the {@link SequentFormula} occurs in this Semisequent (identity check)
     *
     * @param sequentFormula the {@link SequentFormula} to look for
     * @return true iff. sequentFormula has been found in this Semisequent
     */
    public boolean contains(SequentFormula sequentFormula) {
        return indexOf(sequentFormula) != -1;
    }

    /**
     * checks if a {@link SequentFormula} is in this Semisequent (equality check)
     *
     * @param sequentFormula the {@link SequentFormula} to look for
     * @return true iff. sequentFormula has been found in this Semisequent
     */
    public boolean containsEqual(SequentFormula sequentFormula) {
        return seqList.contains(sequentFormula);
    }

    /**
     * returns iterator about the elements of the sequent
     *
     * @return Iterator<SequentFormula>
     */
    @Override
    public Iterator<SequentFormula> iterator() {
        return seqList.iterator();
    }

    public ImmutableList<SequentFormula> asList() {
        return seqList;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof Semisequent)) {
            return false;
        }
        return seqList.equals(((Semisequent) o).seqList);
    }


    @Override
    public int hashCode() {
        return seqList.hashCode();
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

        /**
         * inserts the element always at index 0 ignores the first argument
         *
         * @param idx int encoding the place the element has to be put
         * @param sequentFormula {@link SequentFormula} to be inserted
         * @return semisequent change information object with new semisequent with sequentFormula at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo insert(int idx, SequentFormula sequentFormula) {
            return insertFirst(sequentFormula);
        }

        /**
         * inserts the element at index 0
         *
         * @param sequentFormula {@link SequentFormula} to be inserted
         * @return semisequent change information object with new semisequent with sequentFormula at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo insertFirst(SequentFormula sequentFormula) {
            final SemisequentChangeInfo sci = new SemisequentChangeInfo(
                ImmutableSLList.<SequentFormula>nil().prepend(sequentFormula));
            sci.addedFormula(0, sequentFormula);
            return sci;
        }

        /**
         * inserts the element at the end of the semisequent
         *
         * @param sequentFormula {@link SequentFormula} to be inserted
         * @return semisequent change information object with new semisequent with sequentFormula at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo insertLast(SequentFormula sequentFormula) {
            return insertFirst(sequentFormula);
        }


        /**
         * is this a semisequent that contains no formulas
         *
         * @return true if the semisequent contains no formulas
         */
        @Override
        public boolean isEmpty() {
            return true;
        }

        /**
         * replaces the element at place idx with sequentFormula
         *
         * @param idx an int specifying the index of the element that has to be replaced
         * @param sequentFormula the {@link SequentFormula} replacing the old element at index idx
         * @return semisequent change information object with new semisequent with sequentFormula at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo replace(int idx, SequentFormula sequentFormula) {
            return insertFirst(sequentFormula);
        }

        /** @return int counting the elements of this semisequent */
        @Override
        public int size() {
            return 0;
        }

        /**
         * removes an element
         *
         * @param idx int being the index of the element that has to be removed
         * @return semisequent change information object with an empty semisequent as result
         */
        @Override
        public SemisequentChangeInfo remove(int idx) {
            return new SemisequentChangeInfo(ImmutableSLList.nil());
        }

        /**
         * returns index of a {@link SequentFormula}
         *
         * @param sequentFormula the {@link SequentFormula} the index want to be determined
         * @return index of sequentFormula
         */
        @Override
        public int indexOf(SequentFormula sequentFormula) {
            return -1;
        }

        /**
         * gets the element at a specific index
         *
         * @param idx int representing the index of the element we want to have
         * @return {@link SequentFormula} found at index idx
         */
        @Override
        public SequentFormula get(int idx) {
            return null;
        }

        /**
         * @return the first SequentFormula of this Semisequent
         */
        @Override
        public SequentFormula getFirst() {
            return null;
        }

        /**
         * checks if a {@link SequentFormula} is in this Semisequent
         *
         * @param sequentFormula the {@link SequentFormula} to look for
         * @return true iff. sequentFormula has been found in this Semisequent
         */
        @Override
        public boolean contains(SequentFormula sequentFormula) {
            return false;
        }

        @Override
        public boolean equals(Object o) {
            return o == this;
        }

        @Override
        public int hashCode() {
            return 34567;
        }

        /** @return String representation of this Semisequent */
        @Override
        public String toString() {
            return "[]";
        }
    }
}
