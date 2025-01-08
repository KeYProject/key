/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.prover.sequent.PosInOccurrence;

public record FormulaChangeInfo(PosInOccurrence positionOfModification, org.key_project.prover.sequent.SequentFormula newFormula) {

    public org.key_project.prover.sequent.SequentFormula getOriginalFormula() {
        return positionOfModification().sequentFormula();
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
//spotless:on