/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.Comparator;

/**
 * Compares arrays of comparable objects (e.g., Integer). Returns negative numbers if o1 is less
 * than o2, positive numbers if o2 is less than o1, and 0 if they are equal. If the arrays are equal
 * up to the length of the shorter one, the shorter one is considered less.
 *
 * @author bruns
 */
public final class LexicographicComparator<U> implements Comparator<Comparable<U>[]> {

    @Override
    public int compare(Comparable<U>[] o1, Comparable<U>[] o2) {
        if (o1 == null && o2 == null) {
            return 0;
        }
        if (o1 == null) {
            return Integer.MIN_VALUE + 1;
        }
        if (o2 == null) {
            return Integer.MAX_VALUE;
        }
        for (int i = 0; i < o1.length && i < o2.length; i++) {
            @SuppressWarnings("unchecked")
            int c = o2[i].compareTo((U) o1[i]);
            if (c != 0) {
                return c;
            }
        }
        return Integer.compare(o2.length, o1.length);
    }
}
