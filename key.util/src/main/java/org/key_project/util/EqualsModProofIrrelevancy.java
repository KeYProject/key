/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

/**
 * Interface to check two objects for equality based on their contents.
 * Ignores attributes that are not relevant to the proof (currently: only origin labels).
 *
 * @author Arne Keller
 */
public interface EqualsModProofIrrelevancy {
    /**
     * Checks whether this object and the other object represent the same data, whilst ignoring
     * attributes that are not relevant for the purpose of these objects in the proof.
     *
     * @param obj other object
     * @return whether these objects are equal
     */
    boolean equalsModProofIrrelevancy(Object obj);

    /**
     * Compute a hashcode that represents the proof-relevant fields of this object.
     *
     * @return the hashcode
     */
    int hashCodeModProofIrrelevancy();
}
