/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

/**
 * Interface to check for equality ignoring given properties and to compute according hash codes on
 * terms.
 *
 * @author Tobias Reinhold
 */
public interface TermEqualsModProperty {

    /**
     * Checks whether this object is equal to {@code o} modulo the property described by
     * {@code property}.
     *
     * @param o the object that is checked for equality
     * @param property the property to be ignored in the equality check
     * @return whether this object is equal to <code>o</code>
     */
    boolean equalsModProperty(Object o, TermProperty property);

    /**
     * Computes the hash code according to the given ignored {@code property}.
     *
     * @param property the ignored property according to which the hash code is computed
     * @return the hash code of this object
     */
    int hashCodeModProperty(TermProperty property);
}
