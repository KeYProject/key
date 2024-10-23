/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.pp;

import org.key_project.ncore.sequent.PosInOccurrence;

public class PosInSequent {
    private Range bounds;
    private final boolean sequent;
    private PosInOccurrence posInOcc = null;

    private Range firstRustStatementRange = null;

    /**
     * creates a PosInSequent that points to the whole sequent.
     */
    public static PosInSequent createSequentPos() {
        return new PosInSequent(null, true);
    }

    /**
     * creates a PosInSequent that points to a SequentFormula described by a PosInOccurrence.
     * Additionally a boolean indicates whether the the whole SequentFormula or just the formula is
     * meant.
     *
     * @param posInOcc the PositionInOccurrence describing the SequentFormula and maybe a subterm of
     *        its formula.
     */
    public static PosInSequent createCfmaPos(PosInOccurrence posInOcc) {
        return new PosInSequent(posInOcc, false);
    }


    // use the create... above for getting instances of PosInSequent
    private PosInSequent(PosInOccurrence posInOcc, boolean sequent) {
        this.posInOcc = posInOcc;
        this.sequent = sequent;
    }


    /**
     * sets the bounds, i.e. the start and end positions of the PosInSequent in a string
     * representation of a sequent.
     *
     * @param r the range of character positions
     */
    public void setBounds(Range r) {
        bounds = r;
    }


    /**
     * returns the bounds in a string representation of a sequent
     *
     * @return start position
     */
    public Range getBounds() {
        return bounds;
    }

    /**
     * sets the bounds, i.e. the start and end positions of the first Java statement, of a
     * corresponding Java program in a string representation of the sequent.
     *
     * @param r the range for the first statement in the corresponding program
     */
    public void setFirstRustStatementRange(Range r) {
        firstRustStatementRange = r;
    }

    /**
     * returns the bounds, i.e. the start and end positions of the first Rust statement, of a
     * corresponding Rust program in a string representation of the sequent.
     *
     * @return the range specifying the first statement in the corresponding program
     */
    public Range getFirstRustStatementRange() {
        return firstRustStatementRange;
    }


    /**
     * returns the PosInOccurrence if the PosInSequent marks a SequentFormula or parts of it, null
     * otherwise.
     */
    public PosInOccurrence getPosInOccurrence() {
        return posInOcc;
    }

    /**
     * returns true if the PosInSequent points to a whole Sequent
     */
    public boolean isSequent() {
        return sequent;
    }

    /**
     * returns a string representation of this PosInSequent
     */
    public String toString() {
        if (isSequent()) {
            return "Whole Sequent";
        }
        return String.valueOf(posInOcc);
    }
}
