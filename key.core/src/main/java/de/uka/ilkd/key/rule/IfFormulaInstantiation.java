/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;

import org.key_project.util.EqualsModProofIrrelevancy;


/**
 * This interface represents objects representing an instantiation of one formula of the if-sequence
 * of a taclet.
 */
public interface IfFormulaInstantiation extends EqualsModProofIrrelevancy {

    /**
     * @return the cf this is pointing to
     */
    SequentFormula getConstrainedFormula();

    String toString(Services services);

    @Override
    default boolean equalsModProofIrrelevancy(Object obj) {
        if (!(obj instanceof IfFormulaInstantiation)) {
            return false;
        }
        IfFormulaInstantiation that = (IfFormulaInstantiation) obj;
        return getConstrainedFormula().equalsModProofIrrelevancy(that.getConstrainedFormula());
    }

    @Override
    default int hashCodeModProofIrrelevancy() {
        return getConstrainedFormula().hashCodeModProofIrrelevancy();
    }
}
