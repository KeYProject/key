/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

import org.key_project.logic.Term;

/// A sequent formula is a wrapper around a formula that occurs as top level formula in a sequent.
/// SequentFormula instances have to be unique in the sequent as they are used by PosInOccurrence to
/// determine the exact position. In earlier KeY versions this class was called ConstrainedFormula
/// as
/// it was equipped with an additional constraints. It would be interesting to add more value to
/// this
/// class by providing a way to add additional annotations or to cache local information about the
/// formula.
public class SequentFormula {
    private final Term term;

    /// Cached value for [#hashCode()].
    private final int hashCode;

    /// creates a new SequentFormula
    ///
    /// @param term a formula
    public SequentFormula(Term term) {
        this.term = term;
        this.hashCode = term.hashCode() * 13;
    }

    /// @return the stored Term
    public Term formula() {
        return term;
    }

    /// String representation
    public String toString() {
        return term.toString();
    }

    /// equal if terms and constraints are equal
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj instanceof SequentFormula cmp) {
            return term.equals(cmp.formula());
        }
        return false;
    }

    public int hashCode() {
        return hashCode;
    }
}
