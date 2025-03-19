/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;


/**
 * Interface for term ordering
 */
public interface TermOrdering {

    /**
     * Compare the two given terms
     *
     * @return a number negative, zero or a number positive if <code>p_a</code> is less than, equal,
     *         or greater than <code>p_b</code> regarding the ordering given by the implementing
     *         class
     */
    int compare(Term p_a, Term p_b);
}
