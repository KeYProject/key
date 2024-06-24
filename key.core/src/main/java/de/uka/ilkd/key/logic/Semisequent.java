/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Collection;
import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import static de.uka.ilkd.key.logic.equality.RenamingProperty.RENAMING_PROPERTY;


/**
 * This class represents the succedent or antecendent part of a sequent. It is more or less a list
 * without duplicates and subsumed formulas. This is ensured using method removeRedundancy. In
 * future versions it can be enhanced to do other simplifications. A sequent and so a semisequent
 * has to be immutable.
 */
public class Semisequent implements Iterable<Term> {

    /** the empty semisequent (using singleton pattern) */
    public static final Semisequent EMPTY_SEMISEQUENT = new Empty();
    /** list with the {@link Term}s of the Semisequent */
    private final ImmutableList<Term> seqList;

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
    public Semisequent(ImmutableList<Term> seqList) {
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
    public Semisequent(Collection<Term> seqList) {
        assert !seqList.isEmpty();
        this.seqList = ImmutableList.fromList(seqList);
    }

    /**
     * Create a new Semisequent from an ordered collection of formulas (possibly empty).
     * The provided collection must be redundancy free, i.e., the created sequent must be exactly
     * the same as when creating the
     * sequent by subsequently inserting all formulas.
     *
     * @param seqList list of sequent formulas
     */
    public static Semisequent create(Collection<Term> seqList) {
        if (seqList.isEmpty()) {
            return EMPTY_SEMISEQUENT;
        }
        return new Semisequent(seqList);
    }


    /**
     * creates a new Semisequent with the Semisequent elements in seqList
     */
    public Semisequent(Term seqFormula) {
        assert seqFormula != null;
        this.seqList = ImmutableSLList.<Term>nil().append(seqFormula);
    }


    /**
     * inserts an element at a specified index performing redundancy checks, this may result in
     * returning same semisequent if inserting would create redundancies
     *
     * @param idx int encoding the place the element has to be put
     * @param fml {@link Term} to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insert(int idx, Term fml) {
        return removeRedundance(idx, fml);
    }

    /**
     * inserts the elements of the list at the specified index performing redundancy checks
     *
     * @param idx int encoding the place where the insertion starts
     * @param insertionList IList<Term> to be inserted starting at idx
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insert(int idx, ImmutableList<Term> insertionList) {
        return removeRedundance(idx, insertionList);
    }

    /**
     * inserts element at index 0 performing redundancy checks, this may result in returning same
     * semisequent if inserting would create redundancies
     *
     * @param fml the Term to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insertFirst(Term fml) {
        return insert(0, fml);
    }

    /**
     * inserts element at index 0 performing redundancy checks, this may result in returning same
     * semisequent if inserting would create redundancies
     *
     * @param insertions IList<Term> to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insertFirst(ImmutableList<Term> insertions) {
        return insert(0, insertions);
    }

    /**
     * inserts element at the end of the semisequent performing redundancy checks, this may result
     * in returning same semisequent if inserting would create redundancies
     *
     * @param fml {@link Term} to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insertLast(Term fml) {
        return insert(size(), fml);
    }

    /**
     * inserts the formulas of the list at the end of the semisequent performing redundancy checks,
     * this may result in returning same semisequent if inserting would create redundancies
     *
     * @param insertions the IList<Term> to be inserted
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo insertLast(ImmutableList<Term> insertions) {
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
     * inserts new fml at index idx and removes duplicates, perform simplifications etc.
     *
     * @param fci null if the formula to be added is new, otherwise an object telling which formula
     *        is replaced with the new formula <code>fml</code>, and what are the
     *        differences between the two formulas
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    private SemisequentChangeInfo insertAndRemoveRedundancyHelper(int idx,
            Term fml, SemisequentChangeInfo semiCI, FormulaChangeInfo fci) {

        // Search for equivalent formulas and weakest constraint
        ImmutableList<Term> searchList = semiCI.getFormulaList();
        final Term[] newSeqList = new Term[searchList.size()];
        Term cf;
        int pos = -1;

        while (!searchList.isEmpty()) {
            ++pos;
            cf = searchList.head();
            searchList = searchList.tail();

            if (fml != null) {
                if (cf.equalsModProperty(fml,
                    RENAMING_PROPERTY)) {
                    semiCI.rejectedFormula(fml);
                    return semiCI; // semisequent already contains formula

                }
            }
            newSeqList[pos] = cf;
        }


        // compose resulting formula list
        if (fci == null) {
            semiCI.addedFormula(idx, fml);
        } else {
            semiCI.modifiedFormula(idx, fci);
        }

        final ImmutableList<Term> orig = semiCI.getFormulaList();
        pos = Math.min(idx, orig.size());

        searchList = semiCI.getFormulaList().take(pos).prepend(fml);

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
     * @param TermsToBeInserted the {@link ImmutableList<Term>} to be inserted
     *        at position idx
     * @param idx an int that means insert Term at the idx-th position in the semisequent
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    private SemisequentChangeInfo insertAndRemoveRedundancy(int idx,
            ImmutableList<Term> TermsToBeInserted, SemisequentChangeInfo sci) {

        int pos = idx;
        ImmutableList<Term> oldFormulas = sci.getFormulaList();

        while (!TermsToBeInserted.isEmpty()) {
            final Term aTerm = TermsToBeInserted.head();
            TermsToBeInserted = TermsToBeInserted.tail();

            sci = insertAndRemoveRedundancyHelper(pos, aTerm, sci, null);

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
     * @param Term the IList<Term> to be inserted at position idx
     * @param idx an int that means insert Term at the idx-th position in the semisequent
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    private SemisequentChangeInfo removeRedundance(int idx,
            ImmutableList<Term> Term) {
        return insertAndRemoveRedundancy(idx, Term, new SemisequentChangeInfo(seqList));
    }


    /**
     * . inserts new fml at index {@code idx} and removes duplicates, perform
     * simplifications etc.
     *
     * @param fml the fml to be inserted at position idx
     * @param idx an int that means insert fml at the idx-th position in the semisequent
     * @return new Semisequent with fml at index idx and removed redundancies
     */
    private SemisequentChangeInfo removeRedundance(int idx, Term fml) {
        return insertAndRemoveRedundancyHelper(idx, fml,
            new SemisequentChangeInfo(seqList), null);
    }


    /**
     * replaces the element at place idx with fml
     *
     * @param pos the PosInOccurrence describing the position of and within the formula below which
     *        the formula differs from the new formula <code>fml</code>
     * @param fml the fml replacing the old element at index idx
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo replace(PosInOccurrence pos, Term fml) {
        final int idx = indexOf(pos.sequentLevelFormula());
        final FormulaChangeInfo fci = new FormulaChangeInfo(pos, fml);
        return insertAndRemoveRedundancyHelper(idx, fml, remove(idx), fci);
    }

    /**
     * replaces the <tt>idx</tt>-th formula by <tt>fml</tt>
     *
     * @param idx the int with the position of the formula to be replaced
     * @param fml the fml replacing the formula at the given position
     * @return a SemisequentChangeInfo containing the new sequent and a diff to the old one
     */
    public SemisequentChangeInfo replace(int idx, Term fml) {
        return insertAndRemoveRedundancyHelper(idx, fml, remove(idx), null);
    }

    /**
     * replaces the element at place idx with the first element of the given list and adds the rest
     * of the list to the semisequent behind the replaced formula
     *
     * @param pos the formula to be replaced
     * @param replacements the IList<Term> whose head replaces the element at index idx
     *        and the tail is added to the semisequent
     * @return a semi sequent change information object with the new semisequent and information
     *         which formulas have been added or removed
     */
    public SemisequentChangeInfo replace(PosInOccurrence pos,
            ImmutableList<Term> replacements) {
        final int idx = indexOf(pos.sequentLevelFormula());
        return insertAndRemoveRedundancy(idx, replacements, remove(idx));
    }

    /**
     * replaces the formula at position {@code idx} by the given list of formulas
     *
     * @param idx the position
     * @param replacements the new formulas
     * @return change information including the resulting semisequent after the replacement
     */
    public SemisequentChangeInfo replace(int idx, ImmutableList<Term> replacements) {
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

        ImmutableList<Term> newList = seqList;
        int index = 0;

        if (idx < 0 || idx >= size()) {
            return new SemisequentChangeInfo(seqList);
        }

        final Term[] temp = new Term[idx];

        while (index < idx) {// go to idx
            temp[index] = newList.head();
            newList = newList.tail();
            index++;
        }

        // remove the element that is at head of newList
        final Term removedFormula = newList.head();
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
     * returns the index of the given {@link Term} or {@code -1} if the sequent formula is
     * not found. Identity (not equality) of sequent formulas is checked (i.e.,
     * <code>==</code>)
     *
     * @param fml the {@link Term} to look for
     * @return index of fml (-1 if not found)
     */
    public int indexOf(Term fml) {
        ImmutableList<Term> searchList = seqList;
        int index = 0;
        while (!searchList.isEmpty()) {
            if (searchList.head() == fml) {
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
     * @return {@link Term} found at index idx
     * @throws IndexOutOfBoundsException if idx is negative or greater or equal to
     *         {@link Sequent#size()}
     */
    public Term get(int idx) {
        if (idx < 0 || idx >= seqList.size()) {
            throw new IndexOutOfBoundsException();
        }
        return seqList.take(idx).head();
    }

    /** @return the first {@link Term} of this Semisequent */
    public Term getFirst() {
        return seqList.head();
    }

    /**
     * checks if the {@link Term} occurs in this Semisequent (identity check)
     *
     * @param fml the {@link Term} to look for
     * @return true iff. fml has been found in this Semisequent
     */
    public boolean contains(Term fml) {
        return indexOf(fml) != -1;
    }

    /**
     * checks if a {@link Term} is in this Semisequent (equality check)
     *
     * @param fml the {@link Term} to look for
     * @return true iff. fml has been found in this Semisequent
     */
    public boolean containsEqual(Term fml) {
        return seqList.contains(fml);
    }

    /**
     * returns iterator about the elements of the sequent
     *
     * @return Iterator<Term>
     */
    @Override
    public Iterator<Term> iterator() {
        return seqList.iterator();
    }

    public ImmutableList<Term> asList() {
        return seqList;
    }

    @Override
    public boolean equals(Object o) {
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
         * @param fml {@link Term} to be inserted
         * @return semisequent change information object with new semisequent with fml at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo insert(int idx, Term fml) {
            return insertFirst(fml);
        }

        /**
         * inserts the element at index 0
         *
         * @param fml {@link Term} to be inserted
         * @return semisequent change information object with new semisequent with Term at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo insertFirst(Term fml) {
            final SemisequentChangeInfo sci = new SemisequentChangeInfo(
                ImmutableSLList.<Term>nil().prepend(fml));
            sci.addedFormula(0, fml);
            return sci;
        }

        /**
         * inserts the element at the end of the semisequent
         *
         * @param fml {@link Term} to be inserted
         * @return semisequent change information object with new semisequent with fml at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo insertLast(Term fml) {
            return insertFirst(fml);
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
         * replaces the element at place idx with Term
         *
         * @param idx an int specifying the index of the element that has to be replaced
         * @param fml the {@link Term} replacing the old element at index idx
         * @return semisequent change information object with new semisequent with Term at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo replace(int idx, Term fml) {
            return insertFirst(fml);
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
         * returns index of a {@link Term}
         *
         * @param fml the {@link Term} the index want to be determined
         * @return index of Term
         */
        @Override
        public int indexOf(Term fml) {
            return -1;
        }

        /**
         * gets the element at a specific index
         *
         * @param idx int representing the index of the element we want to have
         * @return {@link Term} found at index idx
         */
        @Override
        public Term get(int idx) {
            return null;
        }

        /**
         * @return the first Term of this Semisequent
         */
        @Override
        public Term getFirst() {
            return null;
        }

        /**
         * checks if a {@link Term} is in this Semisequent
         *
         * @param fml the {@link Term} to look for
         * @return true iff. Term has been found in this Semisequent
         */
        @Override
        public boolean contains(Term fml) {
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
