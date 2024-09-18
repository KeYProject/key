/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.rules;


import org.key_project.logic.LogicServices;
import org.key_project.ncore.sequent.SequentFormula;

public interface AssumesFormulaInstantiation {
    /**
     * @return the cf this is pointing to
     */
    SequentFormula getSequentFormula();

    String toString(LogicServices services);
}
