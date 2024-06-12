/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.equality.ProofIrrelevancyProperty;

import org.key_project.util.EqualsModProofIrrelevancy;


/**
 * This interface represents objects representing an instantiation of one formula of the if-sequence
 * of a taclet.
 */
public interface IfFormulaInstantiation extends EqualsModProofIrrelevancy {

    /**
     * @return the cf this is pointing to
     */
    Term getConstrainedFormula();

    String toString(Services services);

    @Override
    default boolean equalsModProofIrrelevancy(Object obj) {
        if (!(obj instanceof IfFormulaInstantiation that)) {
            return false;
        }
        return getConstrainedFormula().equalsModProperty(that.getConstrainedFormula(),
            ProofIrrelevancyProperty.PROOF_IRRELEVANCY_PROPERTY);
    }

    @Override
    default int hashCodeModProofIrrelevancy() {
        return getConstrainedFormula()
                .hashCodeModProperty(ProofIrrelevancyProperty.PROOF_IRRELEVANCY_PROPERTY);
    }
}
