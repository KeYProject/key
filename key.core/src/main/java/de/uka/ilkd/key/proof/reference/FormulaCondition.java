/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;

public class FormulaCondition implements Condition {
    private final SequentFormula sequentFormula;

    public FormulaCondition(SequentFormula sequentFormula) {
        this.sequentFormula = sequentFormula;
    }

    @Override
    public boolean isFulfilled(Sequent seq) {
        return seq.contains(sequentFormula);
    }
}
