/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;


import java.util.Collection;
import java.util.List;

public final class IntegerUtil {
    /**
     * Forbid instances.
     */
    private IntegerUtil() {
    }

    /**
     * Computes the factorial value of n.
     *
     * @param n The value.
     * @return The computed factorial value or {@code -1} if n is negative.
     */
    public static int factorial(int n) {
        if (n < 0) {
            return -1;
        } else {
            int factorial = 1;
            for (int i = 1; i <= n; i++) {
                factorial *= i;
            }
            return factorial;
        }
    }

    /**
     * Creates a list of integers from {@code 0} (inclusive) to the size of the given collection (exclusive).
     */
    public static List<Integer> indexRangeOf(Collection<?> coll) {
        return rangeUntil(coll.size());
    }

    /**
     * Creates a list of integers from {@code 0} (inclusive) to {@code size} (exclusive).
     */
    private static List<Integer> rangeUntil(int size) {
        return range(0, size);
    }

    /**
     * Creates a list of integers from {@code from} (inclusive) to {@code untilExclusive} (exclusive).
     */
    private static List<Integer> range(int from, int untilExclusive) {
        return java.util.stream.IntStream.range(from, untilExclusive).boxed().toList();
    }
}
