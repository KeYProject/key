/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

public class ProofIrrelevancyProperty implements TermProperty {
    @Override
    public Boolean equalsModThisProperty(Term term, Object o) {
        return null;
    }

    @Override
    public int hashCodeModThisProperty(Term term) {
        throw new UnsupportedOperationException(
            "Hashing of terms modulo proof irrelevancy not yet implemented!");
    }
}
