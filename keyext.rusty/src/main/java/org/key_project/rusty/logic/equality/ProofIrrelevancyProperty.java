/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.equality;

import org.key_project.logic.Term;

public class ProofIrrelevancyProperty implements Property<Term> {
    public static final ProofIrrelevancyProperty PROOF_IRRELEVANCY_PROPERTY =
        new ProofIrrelevancyProperty();

    private ProofIrrelevancyProperty() {}

    @Override
    public <V> boolean equalsModThisProperty(Term term1, Term term2, V... v) {
        if (term2 == term1) {
            return true;
        }
        // TODO: Implement equalsModThisProperty
        return false;
    }

    @Override
    public int hashCodeModThisProperty(Term term) {
        // TODO: Implement hashCodeModThisProperty
        return 0;
    }
}
