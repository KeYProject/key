/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

import java.util.Iterator;
import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;


/// The `Sequent` class represents a formal proof construct consisting of two components:
/// an antecedent and a succedent, which are both instances of [Semisequent].
/// It provides an abstraction for handling proof sequents in a logic-based reasoning framework.
///
/// A `Sequent` has the general structure `antecedent ==> succedent`, where:
/// The `antecedent` and the `succedent` represents collections of formulas.
///
/// Instances of this class are immutable, ensuring that operations such as adding, replacing,
/// or removing formulas result in the creation of new `Sequent` objects rather than
/// modifying existing ones.
/// ## Subclassing
///
/// Subclasses of `Sequent` must implement abstract methods to define specific
/// construction and behavior, including:
///
/// - [#getEmptySequent()] - Returns a canonical empty sequent.
/// - [#createSequent(Semisequent,Semisequent)] - Constructs a new sequent from given
/// antecedent and succedent components.
/// - [#createSemisequent(ImmutableList)] - Constructs a [Semisequent] from a list
/// of formulas.
///
/// ## Immutability
///
/// All mutating operations on a sequent (e.g., adding, removing, or replacing formulas)
/// return a new `Sequent` instance without altering the original object.
///
/// @see Semisequent
/// @see SequentFormula
/// @see ImmutableList
/// @see SequentChangeInfo
/// @see PosInOccurrence
public abstract class Sequent implements Iterable<SequentFormula>, SyntaxElement {

    private final Semisequent antecedent;
    private final Semisequent succedent;

    /// Constructs a new Sequent object with the specified antecedent and succedent.
    /// The sequent represents a logical relationship of the form `antecedent ==> succedent`.
    ///
    /// @param antecedent the [Semisequent] representing the antecedent of the sequent
    /// @param succedent the [Semisequent] representing the succedent of the sequent
    /// @throws AssertionError if both the antecedent and succedent are empty
    protected Sequent(Semisequent antecedent, Semisequent succedent) {
        assert !antecedent.isEmpty() || !succedent.isEmpty();
        this.antecedent = antecedent;
        this.succedent = succedent;
    }

    /// Constructs a new empty Sequent object, used for [NILSequent] implementations.
    ///
    /// @param emptySeq an empty [Semisequent], used as both antecedent and succedent
    /// @throws AssertionError if the provided semisequent is not empty
    protected Sequent(Semisequent emptySeq) {
        assert emptySeq.isEmpty();
        this.antecedent = emptySeq;
        this.succedent = emptySeq;
    }

    /// Computes the total number of formulas in the sequent by summing the sizes
    /// of the antecedent and succedent.
    ///
    /// @return the total number of formulas in the sequent
    public int size() {
        return antecedent().size() + succedent().size();
    }

    /// Retrieves the semisequent representing the antecedent of this sequent.
    ///
    /// @return the [Semisequent] representing the antecedent
    public Semisequent antecedent() {
        return antecedent;
    }

    /// Retrieves the semisequent representing the succedent of this sequent.
    ///
    /// @return the [Semisequent] representing the succedent
    public Semisequent succedent() {
        return succedent;
    }

    /// Provides a string representation of this sequent in the form:
    /// `antecedent ==> succedent`.
    ///
    /// @return a string representation of the sequent
    @Override
    public String toString() {
        return antecedent().toString() + "==>" + succedent().toString();
    }

    /// Creates an iterator to traverse all [SequentFormula] objects in this sequent.
    /// The iterator traverses the antecedent first, followed by the succedent.
    ///
    /// @return an iterator over the formulas in this sequent
    @Override
    public @NonNull Iterator<SequentFormula> iterator() {
        return new SequentIterator(antecedent(), succedent());
    }

    /// Determines whether the formula at the specified position is part of the antecedent.
    ///
    /// @param formulaNumber the 1-based index of the formula (1-based means the first formula has
    /// index 1)
    /// @return `true` if the formula is in the antecedent, `false` otherwise
    /// @throws IllegalArgumentException if the formula number is out of bounds
    public boolean numberInAntecedent(int formulaNumber) {
        checkFormulaIndex(formulaNumber);
        return formulaNumber <= antecedent.size();
    }

    /// Checks whether this sequent contains any formulas.
    ///
    /// @return `true` if the sequent is empty, `false` otherwise
    public boolean isEmpty() {
        return antecedent.isEmpty() && succedent.isEmpty();
    }

    /// Retrieves the formula at the specified 1-based index in the sequent.
    /// Formulas in the antecedent are indexed first, followed by those in the succedent.
    /// 1-based means the index of the first formula is 1.
    ///
    /// @param formulaNumber the 1-based index of the formula to retrieve
    /// @return the [SequentFormula] at the specified position
    /// @throws IllegalArgumentException if the formula number is out of bounds
    public SequentFormula getFormulaByNr(int formulaNumber) {
        checkFormulaIndex(formulaNumber);
        if (formulaNumber <= antecedent.size()) {
            return antecedent.get(formulaNumber - 1);
        }
        return succedent.get((formulaNumber - 1) - antecedent.size());
    }

    /// Adds a formula to the antecedent or succedent of this sequent depending on the
    /// `inAntecedent` flag.
    /// The formula can be added either at the beginning or the end, based on the `first` flag.
    /// (NOTE:Sequent determines index using identity (==) not equality.)
    ///
    /// @param sequentFormula the [SequentFormula] to add
    /// @param inAntecedent `true` to add the formula to the antecedent, `false` for the
    /// succedent
    /// @param first `true` to add the formula at the beginning, `false` to add it at the
    /// end of the
    /// selected semisequent
    /// @return a [SequentChangeInfo] containing the modified sequent and details of the change
    /// like which formulas have been added or removed (removal is possible as the
    /// implementation guarantees
    /// redundance freeness)
    public SequentChangeInfo addFormula(SequentFormula sequentFormula, boolean inAntecedent,
            boolean first) {
        final Semisequent seq = inAntecedent ? antecedent : succedent;

        final SemisequentChangeInfo semiCI =
            first ? seq.insertFirst(sequentFormula) : seq.insertLast(sequentFormula);

        return SequentChangeInfo.createSequentChangeInfo(inAntecedent, semiCI,
            composeSequent(inAntecedent, createSemisequent(semiCI.getFormulaList())),
            this);
    }

    /// Adds a list formulas to the antecedent or succedent of this sequent depending on
    /// the value of the `inAntecedent` flag.
    /// The formulas can be added either at the beginning or the end of the semisequent,
    /// based on the `first` flag.
    ///
    /// (NOTE:Sequent determines index using identity (==) not equality.)
    ///
    /// @param insertions an [ImmutableList] of [SequentFormula]s to add
    /// @param inAntecedent `true` to add the formulas to the antecedent, `false` for the
    /// succedent
    /// @param first `true` to add the formulas at the beginning, `false` to add them at
    /// the end
    /// @return a [SequentChangeInfo] containing the modified sequent and which
    /// formulas have been added or removed
    public SequentChangeInfo addFormula(ImmutableList<SequentFormula> insertions,
            boolean inAntecedent, boolean first) {

        if (insertions.isEmpty()) {
            return SequentChangeInfo.createSequentChangeInfo(this);
        }

        final Semisequent seq = inAntecedent ? this.antecedent : succedent;

        final SemisequentChangeInfo semiCI =
            first ? seq.insertFirst(insertions) : seq.insertLast(insertions);

        return SequentChangeInfo.createSequentChangeInfo(inAntecedent, semiCI,
            composeSequent(inAntecedent, createSemisequent(semiCI.getFormulaList())),
            this);
    }

    /// Replaces the antecedent or succedent of this sequent with a specified [Semisequent].
    ///
    /// @param inAntecedent `true` to replace the antecedent, `false` for the succedent
    /// @param otherSemisequent the [Semisequent] to use as the replacement
    /// @return a new [Sequent] with the updated antecedent or succedent
    protected Sequent composeSequent(boolean inAntecedent, Semisequent otherSemisequent) {

        if ((inAntecedent && otherSemisequent == antecedent()) ||
                (!inAntecedent && otherSemisequent == succedent())) {
            return this;
        }

        final var newAntecedent = inAntecedent ? otherSemisequent : antecedent();
        final var newSuccedent = inAntecedent ? succedent() : otherSemisequent;

        if (newAntecedent.isEmpty() && newSuccedent.isEmpty()) {
            return getEmptySequent();
        } else {
            return createSequent(newAntecedent, newSuccedent);
        }
    }

    /// Returns an instance representing the empty sequent.
    ///
    /// @return an empty sequent
    abstract protected Sequent getEmptySequent();

    /// Creates a new sequent of the shape `newAntecedent ==> newSuccedent`.
    /// Subclassing methods should check whether both semisequents are empty and in that case return
    /// the sequent provided by [#getEmptySequent()].
    ///
    /// @param newAntecedent the [Semisequent] to be used as antecedent
    /// @param newSuccedent the [Semisequent] to be used succedent
    /// @return a [Sequent] composed of the provided semisequents
    abstract protected Sequent createSequent(Semisequent newAntecedent, Semisequent newSuccedent);

    /// Adds a formula to the sequent at the given position.
    ///
    /// (NOTE: Sequent determines index using identity (==) not equality.)
    ///
    ///
    /// @param sequentFormula a [SequentFormula] to be added
    /// @param pos a [PosInOccurrence] describes position in the sequent
    /// @return a [SequentChangeInfo] which contains the new sequent and information which
    /// formulas have been added or removed
    public SequentChangeInfo addFormula(SequentFormula sequentFormula, PosInOccurrence pos) {
        final Semisequent seq = getSemisequent(pos);

        final SemisequentChangeInfo semiCI =
            seq.insert(seq.indexOf(pos.sequentFormula()), sequentFormula);

        return SequentChangeInfo.createSequentChangeInfo(pos.isInAntec(), semiCI,
            composeSequent(pos.isInAntec(),
                createSemisequent(semiCI.getFormulaList())),
            this);
    }

    /// creates a semisequent from the provided change information object
    ///
    /// @param semiCI the change information describing the semisequent resulting from modifications
    /// of an
    /// existing one
    ///
    /// @return a [Semisequent] representing the semisequent described by the change object
    private Semisequent createSemisequent(SemisequentChangeInfo semiCI) {
        return createSemisequent(semiCI.getFormulaList());
    }

    /// Creates a new [Semisequent] composed of the list of formulas proved as argument
    ///
    /// @param formulas the {@ImmutableList} of [SequentFormula]s used to create the
    /// semisequent
    /// @return the [Semisequent] consisting of the provided formulas
    abstract protected Semisequent createSemisequent(final ImmutableList<SequentFormula> formulas);


    /// Replaces a formula at the specified index.
    ///
    /// @param formulaNr where to replace the formula
    /// @param replacement the new sequent formula
    /// @return a SequentChangeInfo which contains the new sequent and information which formulas
    /// have been added or removed
    public SequentChangeInfo replaceFormula(int formulaNr, SequentFormula replacement) {
        checkFormulaIndex(formulaNr);
        formulaNr--;
        boolean inAntecedent = formulaNr < antecedent.size();

        Semisequent seq = inAntecedent ? antecedent : succedent;
        int idx = inAntecedent ? formulaNr : formulaNr - antecedent.size();

        final SemisequentChangeInfo semiCI = seq.replace(idx, replacement);

        return SequentChangeInfo.createSequentChangeInfo(inAntecedent, semiCI,
            composeSequent(inAntecedent, createSemisequent(semiCI)), this);
    }

    /// adds the formulas of list insertions to the sequent starting at position `pos`.
    /// (NOTE:Sequent
    /// determines index using identity (==) not equality.)
    ///
    /// @param insertions an [ImmutableList] of [SequentFormula]s with the formulas to be
    /// added
    /// @param pos the [PosInOccurrence] describing the position where to insert the formulas
    /// @return a [SequentChangeInfo] which contains the new sequent and information which
    /// formulas
    /// have been added or removed
    public SequentChangeInfo addFormula(ImmutableList<SequentFormula> insertions,
            PosInOccurrence pos) {
        final Semisequent seq = getSemisequent(pos);

        final SemisequentChangeInfo semiCI =
            seq.insert(seq.indexOf(pos.sequentFormula()), insertions);

        return SequentChangeInfo.createSequentChangeInfo(pos.isInAntec(), semiCI,
            composeSequent(pos.isInAntec(), createSemisequent(semiCI)), this);
    }

    /// removes the formula at position `pos` (NOTE:Sequent determines index using identity
    /// (==) not
    /// equality.)
    ///
    /// @param pos a [PosInOccurrence] that describes position in the sequent
    /// @return a [SequentChangeInfo] which contains the new sequent and information which
    /// formulas
    /// have been added or removed
    public SequentChangeInfo removeFormula(PosInOccurrence pos) {
        final Semisequent seq = getSemisequent(pos);

        final SemisequentChangeInfo semiCI = seq.remove(seq.indexOf(pos.sequentFormula()));

        return SequentChangeInfo.createSequentChangeInfo(pos.isInAntec(),
            semiCI, composeSequent(pos.isInAntec(), createSemisequent(semiCI)), this);
    }

    /// returns the [Semisequent] in which the [SequentFormula] described by
    /// [PosInOccurrence] `pos` occurs
    private Semisequent getSemisequent(PosInOccurrence pos) {
        return pos.isInAntec() ? antecedent() : succedent();
    }

    /// replaces the formula at position `pos` with the head of the given list and adds the
    /// remaining
    /// list elements to the sequent (NOTE: Sequent determines index using identity (==) not
    /// equality.)
    ///
    /// @param replacements the [ImmutableList] of [SequentFormula]s whose head replaces
    /// the formula at position `pos` and adds the rest of the list behind
    /// the changed formula
    /// @param pos a [PosInOccurrence] describing the position of the formula to be replaced
    /// @return a [SequentChangeInfo] which contains the new sequent and information which
    /// formulas
    /// have been added or removed
    public SequentChangeInfo changeFormula(ImmutableList<SequentFormula> replacements,
            PosInOccurrence pos) {
        final SemisequentChangeInfo semiCI = getSemisequent(pos).replace(pos, replacements);
        return SequentChangeInfo.createSequentChangeInfo(pos.isInAntec(),
            semiCI, composeSequent(pos.isInAntec(), createSemisequent(semiCI)), this);
    }

    /// replaces the formula at the given position with another one (NOTICE:Sequent determines index
    /// using identity (==) not equality.)
    ///
    /// @param newCF the SequentFormula replacing the old one
    /// @param p a PosInOccurrence describes position in the sequent
    /// @return a SequentChangeInfo which contains the new sequent and information which formulas
    /// have been added or removed
    public SequentChangeInfo changeFormula(SequentFormula newCF, PosInOccurrence p) {
        final SemisequentChangeInfo semiCI = getSemisequent(p).replace(p, newCF);

        return SequentChangeInfo.createSequentChangeInfo(p.isInAntec(), semiCI,
            composeSequent(p.isInAntec(), createSemisequent(semiCI.getFormulaList())),
            this);
    }

    /// Computes the position of the given sequent formula on the proof sequent, starting with one
    /// for the very first sequent formula.
    ///
    /// @param inAntecedent a boolean stating whether we search in the antecedent or the succedent
    /// @param sequentFormula the given sequent formula
    /// @return an integer strictly greater than zero for the position of the given sequent formula
    /// on the proof sequent.
    public int formulaNumberInSequent(boolean inAntecedent, SequentFormula sequentFormula) {
        int n = inAntecedent ? 0 : antecedent.size();
        final Iterator<SequentFormula> semisequentIterator =
            inAntecedent ? antecedent.iterator() : succedent.iterator();
        while (semisequentIterator.hasNext()) {
            n++;
            if (semisequentIterator.next().equals(sequentFormula)) {
                return n;
            }
        }
        throw new RuntimeException(
            "Ghost formula " + sequentFormula + " in sequent " + this + " [antec=" + inAntecedent
                + "]");
    }

    /// Computes the position of the given [PosInOccurrence] on the proof sequent.
    ///
    /// @param pio the position
    /// @return an integer strictly greater than zero for the position of the given sequent formula
    /// on the proof sequent.
    public int formulaNumberInSequent(PosInOccurrence pio) {
        return formulaNumberInSequent(pio.isInAntec(), pio.sequentFormula());
    }

    protected static abstract class NILSequent extends Sequent {

        protected NILSequent(Semisequent emptySemisequent) {
            super(emptySemisequent);
        }

        @Override
        public boolean isEmpty() {
            return true;
        }

        @Override
        public @NonNull Iterator<SequentFormula> iterator() {
            return ImmutableSLList.<SequentFormula>nil().iterator();
        }
    }

    static class SequentIterator implements Iterator<SequentFormula> {
        /// The iterator over the antecedent of the proof sequent.
        private final Iterator<SequentFormula> antecedentIterator;
        /// The iterator over the succedent of the proof sequent.
        private final Iterator<SequentFormula> succedentIterator;

        /// Constructs a new iterator over a proof sequent.
        ///
        /// @param antecedent The antecedent of the sequent.
        /// @param succedent The succedent of the sequent.
        SequentIterator(Semisequent antecedent, Semisequent succedent) {
            this.antecedentIterator = antecedent.iterator();
            this.succedentIterator = succedent.iterator();
        }

        @Override
        public boolean hasNext() {
            return antecedentIterator.hasNext() || succedentIterator.hasNext();
        }

        @Override
        public SequentFormula next() {
            if (antecedentIterator.hasNext()) {
                return antecedentIterator.next();
            }
            return succedentIterator.next();
        }

        /// throw an unsupported operation exception as sequents are immutable
        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    /// Check that the provided formula number is a 1-based index and in bounds.
    /// Throws an [IllegalArgumentException] otherwise.
    ///
    /// @param formulaNumber the formula number
    private void checkFormulaIndex(int formulaNumber) {
        if (formulaNumber <= 0 || formulaNumber > size()) {
            throw new IllegalArgumentException(
                "No formula nr. " + formulaNumber + " in seq. " + this);
        }
    }

    @Override
    public boolean equals(@Nullable Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof Sequent o1)) {
            return false;
        }
        return Objects.equals(antecedent, o1.antecedent) && Objects.equals(succedent, o1.succedent);
    }

    /// used to check whether this sequent contains a given sequent formula.
    ///
    /// @param formula the given formula
    /// @return true if this sequent contains the given formula
    public boolean contains(SequentFormula formula) {
        return antecedent().contains(formula) || succedent().contains(formula);
    }

    /// Returns a list containing every [SequentFormula] in this sequent.
    ///
    /// @return a list containing every [SequentFormula] in this sequent.
    public ImmutableList<SequentFormula> asList() {
        return antecedent().asList().append(succedent().asList());
    }

    @Override
    public int getChildCount() {
        return size();
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        // Could also make SequentFormula a SyntaxElement; no special reason for current decision.
        return getFormulaByNr(n - 1).formula();
    }
}
