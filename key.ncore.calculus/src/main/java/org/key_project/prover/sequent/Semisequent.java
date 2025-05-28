/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

/// Implements a redundancy free list of sequent formulas
public abstract class Semisequent implements Iterable<SequentFormula> {

    /// list with the [SequentFormula]s of the [Semisequent]
    private final ImmutableList<SequentFormula> seqList;

    /// Create a new [Semisequent] from an ordered collection of formulas.
    /// The provided list must be redundancy free, i.e., the created sequent must be exactly
    /// the same as when creating the sequent by subsequently inserting all formulas
    ///
    /// @param seqList list of sequent formulas
    protected Semisequent(ImmutableList<SequentFormula> seqList) {
        assert !seqList.isEmpty();
        this.seqList = seqList;
    }

    /// used by inner class Empty
    protected Semisequent() {
        seqList = ImmutableSLList.nil();
    }

    /// creates a new [Semisequent] with the [Semisequent] elements in seqList
    private Semisequent(SequentFormula seqFormula) {
        this(ImmutableSLList.singleton(seqFormula));
    }

    /// inserts an element at a specified index performing redundancy checks, this may result in
    /// returning same [Semisequent] if inserting would create redundancies
    ///
    /// @param idx int encoding the place the element has to be put
    /// @param sequentFormula [SequentFormula] to be inserted
    /// @return a semi sequent change information object with the new [Semisequent] and
    /// information, which formulas have been added or removed
    public SemisequentChangeInfo insert(int idx, SequentFormula sequentFormula) {
        return insertAndRemoveRedundancyHelper(idx, sequentFormula,
            createSemisequentChangeInfo(seqList), null);
    }

    /// inserts element at index 0 performing redundancy checks, this may result in returning same
    /// [Semisequent] if inserting would create redundancies
    ///
    /// @param sequentFormula SequentFormula to be inserted
    /// @return a semi sequent change information object with the new semisequent and information
    /// which formulas have been added or removed
    public SemisequentChangeInfo insertFirst(SequentFormula sequentFormula) {
        return insert(0, sequentFormula);
    }

    /// Checks whether this is a [Semisequent] that contains no formulas
    ///
    /// @return true if the [Semisequent] contains no formulas
    public boolean isEmpty() {
        return seqList.isEmpty();
    }

    protected abstract boolean isRedundant(SequentFormula existingFormula,
            SequentFormula checkedFormula);

    /// Inserts a new [SequentFormula] at index `idx` and removes redundant formulas.
    /// This implementation removes only duplicates but the original idea was to realize backward
    /// and forward subsumption.
    ///
    /// @param idx the int specifying where to place the formula (if the formula does not already
    /// occur in the corresponding [Semisequent]
    /// @param sequentFormula the [SequentFormula] to be inserted
    /// @param semiCI the [SemisequentChangeInfo] which describes the current status of the
    /// modified [Semisequent] and which will be updated to reflect the change
    /// performed by the execution of this method invocation
    /// @param fci null if the formula to be added is new, otherwise an object telling which formula
    /// is replaced with the new formula <code>sequentFormula</code>, and what are the
    /// differences between the two formulas
    /// @return a semi sequent change information object with the new [Semisequent] and
    /// information, which formulas have been added or removed
    protected SemisequentChangeInfo insertAndRemoveRedundancyHelper(int idx,
            @NonNull SequentFormula sequentFormula, SemisequentChangeInfo semiCI,
            FormulaChangeInfo fci) {
        // Search for equivalent formulas and weakest constraint
        ImmutableList<SequentFormula> searchList = semiCI.getFormulaList();
        final var newSeqList = new SequentFormula[searchList.size()];
        SequentFormula sf;
        int pos = -1;

        while (!searchList.isEmpty()) {
            ++pos;
            sf = searchList.head();
            searchList = searchList.tail();

            if (sequentFormula != null && isRedundant(sf, sequentFormula)) {
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
            searchList = searchList.prepend(newSeqList[pos]);
        }

        // add new formula list to result object
        semiCI.setFormulaList(searchList);

        return semiCI;
    }

    /// A factory method to provide an entry point to allow subclasses to create more specific
    /// change information if necessary. At the moment final (if flexibility needed, remove the
    /// final
    /// modifier)
    ///
    /// @param seqList the list of the formulas considered to be the starting point from which on
    /// changes are tracked
    /// @return a fresh change information object
    protected final SemisequentChangeInfo createSemisequentChangeInfo(
            ImmutableList<SequentFormula> seqList) {
        return new SemisequentChangeInfo(seqList);
    }

    /// Inserts new [SequentFormula]s starting at index `idx` and removes duplicates,
    /// perform simplifications etc.
    ///
    /// @param idx an int that means insert sequentFormula at the idx-th position in the semisequent
    /// @param sequentFormulasToBeInserted the [ImmutableList] of [SequentFormula]s to
    /// be inserted at position idx
    /// @return a semisequent change information object with the new [Semisequent] and
    /// information which formulas have been added or removed
    private SemisequentChangeInfo insertAndRemoveRedundancy(int idx,
            ImmutableList<SequentFormula> sequentFormulasToBeInserted,
            SemisequentChangeInfo sci) {

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

    /// Retrieves the element at a specific index
    ///
    /// @param idx int representing the index of the element we want to have
    /// @return [SequentFormula] found at index idx
    /// @throws IndexOutOfBoundsException if idx is negative or greater or equal to
    /// [#size()]
    public SequentFormula get(int idx) {
        if (idx < 0 || idx >= seqList.size()) {
            throw new IndexOutOfBoundsException();
        }
        return seqList.take(idx).head();
    }

    /// @return the first [SequentFormula] of this [Semisequent]
    public SequentFormula getFirst() {
        return seqList.head();
    }

    /// Returns iterator about the formulas contained in this [Semisequent]
    ///
    /// @return iterator about the formulas contained in this [Semisequent]
    @Override
    public @NonNull Iterator<SequentFormula> iterator() {
        return seqList.iterator();
    }

    /// Returns the list of sequent formulas constituting this [Semisequent]
    ///
    /// @return an [ImmutableList] of [SequentFormula]s contained in this
    /// [Semisequent]
    public ImmutableList<SequentFormula> asList() {
        return seqList;
    }

    /// Returns the number of formulas of this [Semisequent]
    ///
    /// @return number of formulas of this [Semisequent]
    public int size() {
        return seqList.size();
    }


    /// Two [Semisequent]s are equal if they contain the same formulas in the same order.
    ///
    /// @param other the [Object] to which this [Semisequent] is compared
    /// @return true if and only if the `other` [Semisequent] contains the same
    /// formulas in the same order.
    @Override
    public boolean equals(Object other) {
        if (!(other instanceof Semisequent s)) {
            return false;
        }
        return seqList.equals(s.seqList);
    }

    /// @return String representation of this [Semisequent]
    @Override
    public String toString() {
        return seqList.toString();
    }

    /// Inserts the elements of the list at the specified index performing redundancy checks
    ///
    /// @param idx int encoding the place where the insertion starts
    /// @param insertions the [ImmutableList] of [SequentFormula] to be inserted
    /// @return a semi sequent change information object with the new [Semisequent]
    /// and information, which formulas have been added or removed
    public SemisequentChangeInfo insert(int idx,
            ImmutableList<SequentFormula> insertions) {
        return insertAndRemoveRedundancy(idx, insertions, createSemisequentChangeInfo(seqList));
    }

    /// Inserts element at the end of the semisequent performing redundancy checks, this may result
    /// in returning same semisequent if inserting would create redundancies
    ///
    /// @param sequentFormula [SequentFormula] to be inserted
    /// @return a semi sequent change information object with the new semisequent and information
    /// which formulas have been added or removed
    public SemisequentChangeInfo insertLast(SequentFormula sequentFormula) {
        return insert(size(), sequentFormula);
    }

    /// Returns the index of the given [SequentFormula] or `-1` if the sequent formula is
    /// not found. Equality of sequent formulas is checked sing the identity check (i.e.,
    /// `==`)
    ///
    /// @param sequentFormula the [SequentFormula] to look for
    /// @return index of sequentFormula (-1 if not found)
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

    /// Inserts element at index 0 performing redundancy checks, this may result in returning same
    /// [Semisequent] if inserting would create redundancies
    ///
    /// @param insertions the [ImmutableList] of [SequentFormula] to be inserted
    /// @return a semi sequent change information object with the new [Semisequent] and
    /// information, which formulas have been added or removed
    public SemisequentChangeInfo insertFirst(ImmutableList<SequentFormula> insertions) {
        return insert(0, insertions);
    }

    /// inserts the formulas of the list at the end of the semisequent performing redundancy checks,
    /// this may result in returning same semisequent if inserting would create redundancies
    ///
    /// @param insertions the [ImmutableList] of [SequentFormula] to be inserted
    /// @return a semi sequent change information object with the new [Semisequent] and
    /// information, which formulas have been added or removed
    public SemisequentChangeInfo insertLast(ImmutableList<SequentFormula> insertions) {
        return insert(size(), insertions);
    }

    /// replaces the element at place idx with the first element of the given list and adds the rest
    /// of the list to the semisequent behind the replaced formula
    ///
    /// @param pos the formula to be replaced
    /// @param replacements the IList<SequentFormula> whose head replaces the element at index idx
    /// and the tail is added to the semisequent
    /// @return a semi sequent change information object with the new semisequent and information
    /// which formulas have been added or removed
    public SemisequentChangeInfo replace(PosInOccurrence pos,
            ImmutableList<SequentFormula> replacements) {
        final int idx = indexOf(pos.sequentFormula());
        return insertAndRemoveRedundancy(idx, replacements, remove(idx));
    }

    /// removes an element
    ///
    /// @param idx int being the index of the element that has to be removed
    /// @return a semi sequent change information object with the new semisequent and information
    /// which formulas have been added or removed
    public SemisequentChangeInfo remove(int idx) {
        ImmutableList<SequentFormula> newList = seqList;
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
        final SequentFormula removedFormula = newList.head();
        newList = newList.tail();

        for (int k = index - 1; k >= 0; k--) {
            newList = newList.prepend(temp[k]);
        }

        // create change info object
        final SemisequentChangeInfo sci = createSemisequentChangeInfo(newList);
        sci.removedFormula(idx, removedFormula);

        return sci;
    }

    /// replaces the element at place idx with sequentFormula
    ///
    /// @param pos the PosInOccurrence describing the position of and within the formula below which
    /// the formula differs from the new formula <code>sequentFormula</code>
    /// @param sequentFormula the SequentFormula replacing the old element at index idx
    /// @return a semi sequent change information object with the new semisequent and information
    /// which formulas have been added or removed
    public SemisequentChangeInfo replace(PosInOccurrence pos, SequentFormula sequentFormula) {
        final int idx = indexOf(pos.sequentFormula());
        final FormulaChangeInfo fci = new FormulaChangeInfo(pos, sequentFormula);
        return insertAndRemoveRedundancyHelper(idx, sequentFormula, remove(idx), fci);
    }

    /// replaces the element at place idx with sequentFormula
    ///
    /// @param idx an int specifying the index of the element that has to be replaced
    /// @param sequentFormula the [SequentFormula] replacing the old element at index idx
    /// @return semisequent change information object with new semisequent with sequentFormula at
    /// place idx
    public SemisequentChangeInfo replace(int idx, SequentFormula sequentFormula) {
        return insertAndRemoveRedundancyHelper(idx, sequentFormula, remove(idx), null);
    }

    /// replaces the formula at position `idx` by the given list of formulas
    ///
    /// @param idx the position
    /// @param replacements the new formulas
    /// @return change information including the resulting semisequent after the replacement
    public SemisequentChangeInfo replace(int idx, ImmutableList<SequentFormula> replacements) {
        return insertAndRemoveRedundancy(idx, replacements, remove(idx));
    }

    /// checks if the [SequentFormula] occurs in this [Semisequent] (identity check)
    ///
    /// @param sequentFormula the [SequentFormula] to look for
    /// @return true iff. sequentFormula has been found in this [Semisequent]
    public boolean contains(SequentFormula sequentFormula) {
        return indexOf(sequentFormula) != -1;
    }

    /// checks if a [SequentFormula] is in this [Semisequent] (equality check)
    ///
    /// @param sequentFormula the [SequentFormula] to look for
    /// @return true iff. sequentFormula has been found in this [Semisequent]
    public boolean containsEqual(SequentFormula sequentFormula) {
        return seqList.contains(sequentFormula);
    }
}
