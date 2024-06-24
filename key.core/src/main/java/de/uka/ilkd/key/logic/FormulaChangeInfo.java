/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

/**
 * This class is used to hold information about modified formulas.
 *
 * @param positionOfModification position within the original formula
 * @param newFormula             modified formula
 * @see SequentChangeInfo
 */
public record FormulaChangeInfo(PosInOccurrence positionOfModification, Term newFormula) {

    public Term getOriginalFormula() {
        return positionOfModification().sequentLevelFormula();
    }

    /**
     * @return position within the original formula
     */
    @Override
    public PosInOccurrence positionOfModification() {
        return positionOfModification;
    }

    public String toString() {
        return "Replaced " + positionOfModification + " with " + newFormula;
    }
}
