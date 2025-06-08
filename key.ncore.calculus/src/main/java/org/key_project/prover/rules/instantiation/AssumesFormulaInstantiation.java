/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.instantiation;

import org.key_project.logic.LogicServices;
import org.key_project.prover.sequent.SequentFormula;

/// represents an instantiation of a formula that is part of the taclet's
/// assumes sequent
public interface AssumesFormulaInstantiation {
    /// @return the sequent formula that is the instantiation of one of the formulas
    /// in the taclet's assumes sequent
    SequentFormula getSequentFormula();

    String toString(LogicServices services);
}
