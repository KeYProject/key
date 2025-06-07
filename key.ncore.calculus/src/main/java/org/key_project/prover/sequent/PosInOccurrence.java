/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

import org.key_project.logic.IntIterator;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;

import org.jspecify.annotations.NonNull;

/// Represents a position within a formula contained in a sequent. It enables navigation and
/// analysis
/// of term structures.
public class PosInOccurrence {

    /// Creates a new [PosInOccurrence] for a specific position in a formula within the given
    /// sequent.
    ///
    /// @param seq The sequent containing the formula.
    /// @param formulaNumber The index of the formula within the sequent (the first formula has
    /// number 1).
    /// @param pos The position within the formula to be represented.
    /// @return A new [PosInOccurrence] pointing to the specified position in the formula.
    public static PosInOccurrence findInSequent(Sequent seq, int formulaNumber, PosInTerm pos) {
        return new PosInOccurrence(seq.getFormulaByNr(formulaNumber), pos,
            seq.numberInAntecedent(formulaNumber));
    }

    // saves 8 bytes (due to alignment issues) per instance if we use a
    // short here instead of an int
    private final short hashCode;

    /// the constrained formula the pos in occurrence describes
    private final SequentFormula sequentFormula;
    /// is true iff the position is in the antecedent of a sequent.
    private final boolean inAntec;

    /// the position in sequentFormula.formula()
    private final PosInTerm posInTerm;

    /// The subterm this object points to, or <code>null</code>
    private volatile Term subTermCache = null;

    /// Constructs a [PosInOccurrence] representing a position in a sequent formula.
    ///
    /// @param sequentFormula The formula the position belongs to.
    /// @param posInTerm The position within the formula.
    /// @param inAntec True if the position is within the antecedent of the sequent.
    /// @throws NullPointerException If `sequentFormula` or `posInTerm` is null.
    public PosInOccurrence(@NonNull SequentFormula sequentFormula, @NonNull PosInTerm posInTerm,
            boolean inAntec) {
        assert posInTerm != null;
        assert sequentFormula != null;
        this.inAntec = inAntec;
        this.sequentFormula = sequentFormula;
        this.posInTerm = posInTerm;
        this.hashCode = (short) (sequentFormula.hashCode() * 13 + posInTerm.hashCode());
    }

    /// Retrieves the formula associated with this position.
    ///
    /// @return The [SequentFormula] this position refers to.
    public SequentFormula sequentFormula() {
        return sequentFormula;
    }

    /// Computes the depth of this position within the formula. Top-level positions (see
    /// [#isTopLevel()])
    /// have a depth of 0.
    ///
    /// @return The depth of the position.
    public int depth() {
        return posInTerm().depth();
    }

    /// /**
    /// Moves up one level in the term structure and returns a new [PosInOccurrence]
    /// representing the new position.
    ///
    /// @return A new [PosInOccurrence] one level higher in the term structure.
    /// @throws IllegalStateException If the position is already at the top level.
    public PosInOccurrence up() {
        assert !isTopLevel() : "not possible to go up from top level position";
        return new PosInOccurrence(sequentFormula, posInTerm.up(), inAntec);
    }

    /// Moves down to the specified child in the term structure and returns a new
    /// [PosInOccurrence]
    /// representing the new position.
    ///
    /// @param i The index of the child to move to.
    /// @return A new [PosInOccurrence] pointing to the specified child.
    public PosInOccurrence down(int i) {
        return new PosInOccurrence(sequentFormula, posInTerm.down(i), inAntec);
    }

    /// Retrieves the index of the deepest subterm this position points to.
    /// Returns -1 if the position is top-level.
    ///
    /// @return The index of the subterm or -1 if at the top level.
    public int getIndex() {
        return posInTerm.getIndex();
    }

    /// Determines whether this position is in the antecedent of the sequent.
    ///
    /// @return True if the position is in the antecedent, otherwise false.
    public boolean isInAntec() {
        return inAntec;
    }

    /// Checks if this position is at the top level of the formula.
    ///
    /// @return True if the position is at the top level, otherwise false.
    public boolean isTopLevel() {
        return posInTerm == PosInTerm.getTopLevel();
    }


    /// The usage of this method is strongly discouraged, use [#iterator]
    /// instead. describes the exact occurrence of the referred term inside
    /// [#formula()]
    ///
    /// @return the position in the formula of the SequentFormula of this [PosInOccurrence].
    public PosInTerm posInTerm() {
        return posInTerm;
    }

    /// Moves to the top level of the formula and returns a new [PosInOccurrence] for that
    /// position.
    ///
    /// @return A `PosInOccurrence` representing the top level.
    public PosInOccurrence topLevel() {
        if (isTopLevel()) {
            return this;
        }
        return new PosInOccurrence(sequentFormula, PosInTerm.getTopLevel(), inAntec);
    }

    /// Retrieves the subterm pointed to by this position.
    ///
    /// @return The [Term] at this position.
    public Term subTerm() {
        if (subTermCache == null) {
            subTermCache = posInTerm.getSubTerm(sequentFormula.formula());
        }
        return subTermCache;
    }

    /// Compares this [PosInOccurrence] with another object for equality based on their
    /// contents.
    ///
    /// @param obj The object to compare with.
    /// @return True if the two objects describe the same occurrence, otherwise false.
    public boolean eqEquals(Object obj) {
        if (!(obj instanceof PosInOccurrence cmp)) {
            return false;
        }

        if (!sequentFormula.equals(cmp.sequentFormula)) {
            return false;
        }

        return equalsHelp(cmp);
    }

    /// Checks if this [PosInOccurrence] refers to the exact same formula as another
    /// and to an equal position within this formula.
    ///
    /// @param obj The object to compare with.
    /// @return True if both refer to the same formula, otherwise false.
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof PosInOccurrence cmp)) {
            return false;
        }

        // NB: the class <code>NonDuplicateAppFeature</code> depends on the usage
        // of <code>!=</code> in this condition
        if (sequentFormula() != cmp.sequentFormula()) {
            return false;
        }

        return equalsHelp(cmp);
    }

    private boolean equalsHelp(final PosInOccurrence cmp) {
        if (inAntec == cmp.inAntec) {
            return posInTerm.equals(cmp.posInTerm);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    /// Replaces the formula associated with this occurrence and returns a new object pointing
    /// to the same position within the new formula.
    ///
    /// @param p_newFormula The new formula.
    /// @return A [PosInOccurrence] pointing to the same position in the new formula. It is not
    /// tested
    /// whether this position exists within `p_newFormula`
    public PosInOccurrence replaceSequentFormula(SequentFormula p_newFormula) {
        assert p_newFormula != null;
        if (p_newFormula == sequentFormula) {
            return this;
        }
        return new PosInOccurrence(p_newFormula, posInTerm, inAntec);
    }

    /// Returns an iterator for traversing the path of this position within the term structure.
    ///
    /// @return A [PIOPathIterator] for traversing this position.
    public PIOPathIterator iterator() {
        return new PIOPathIteratorImpl();
    }

    private final class PIOPathIteratorImpl implements PIOPathIterator {
        int child;
        int count = 0;
        IntIterator currentPathIt;
        Term currentSubTerm = null;

        private PIOPathIteratorImpl() {
            currentPathIt = posInTerm().iterator();
        }

        /// @return the number of the next child on the path, or <code>-1</code> if no further child
        /// exists (this is the number that was also returned by the last call of
        /// <code>next()</code>)
        public int getChild() {
            return child;
        }

        public String toString() {
            return "Term " + posInTerm() + " of " + sequentFormula();
        }

        /// @return the current position within the term (i.e. corresponding to the latest
        /// <code>next()</code>-call)
        public PosInOccurrence getPosInOccurrence() {
            // the object is created only now to make the method
            // <code>next()</code> faster

            final PosInOccurrence pio;
            pio = new PosInOccurrence(sequentFormula, posInTerm.firstN(count - 1), inAntec);


            return pio;
        }

        /// @return the current subterm this object points to (i.e. corresponding to the latest
        /// <code>next()</code>-call); this method satisfies
        /// <code>getPosInOccurrence().subTerm()==getSubTerm()</code>
        public Term getSubTerm() {
            return currentSubTerm;
        }

        public boolean hasNext() {
            return currentPathIt != null;
        }

        /// @return the number of the next child on the path, or <code>-1</code> if no further child
        /// exists
        public int next() {
            int res;

            if (currentSubTerm == null) {
                currentSubTerm = sequentFormula.formula();
            } else {
                currentSubTerm = currentSubTerm.sub(child);
            }

            if (currentPathIt.hasNext()) {
                res = currentPathIt.next();
            } else {
                res = -1;
                currentPathIt = null;
            }

            child = res;
            ++count;
            return res;
        }
    }
}
