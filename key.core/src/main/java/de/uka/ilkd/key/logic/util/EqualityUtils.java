/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.util;

import java.util.function.ToIntFunction;

import de.uka.ilkd.key.logic.equality.EqualsModProperty;

public class EqualityUtils {

    /**
     * Computes the hashcode modulo a given property of an iterable of elements that implement
     * {@link EqualsModProperty}.
     *
     * @param iter iterable of terms
     * @return combined hashcode
     */
    public static <T> int hashCodeModPropertyOfIterable(
            Iterable<? extends T> iter,
            ToIntFunction<T> hasher) {
        // adapted from Arrays.hashCode
        if (iter == null) {
            return 0;
        }

        int result = 1;

        for (T element : iter) {
            result = 31 * result + (element == null ? 0
                    : hasher.applyAsInt(element));
        }

        return result;
    }
}
