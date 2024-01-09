/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.logic.Term;

public class EqualityUtils {

    /**
     * Computes the hashcode of an iterable of terms modulo a given property using the elements'
     * {@link TermEqualsModProperty} implementation.
     *
     * @param iter iterable of terms
     * @return combined hashcode
     */
    public static int hashCodeModPropertyOfIterable(TermProperty property,
            Iterable<? extends Term> iter) {
        // adapted from Arrays.hashCode
        if (iter == null) {
            return 0;
        }

        int result = 1;

        for (Term element : iter) {
            result = 31 * result + (element == null ? 0
                    : element.hashCodeModProperty(property));
        }

        return result;
    }
}
