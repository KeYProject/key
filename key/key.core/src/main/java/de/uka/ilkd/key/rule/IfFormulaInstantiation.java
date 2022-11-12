/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;


/*
 * This interface represents objects representing an instantiation of one formula of the if-sequence
 * of a taclet.
 */

public interface IfFormulaInstantiation {

    /**
     * @return the cf this is pointing to
     */
    SequentFormula getConstrainedFormula();

    String toString(Services services);
}
