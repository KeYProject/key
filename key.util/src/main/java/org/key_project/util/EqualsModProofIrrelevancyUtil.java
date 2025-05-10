/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.Objects;
import java.util.function.*;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

/**
 * Utility methods for the equals mod proof irrelevancy check.
 *
 * @author Arne Keller
 */
@SuppressWarnings("nullness")
public final class EqualsModProofIrrelevancyUtil {
    private EqualsModProofIrrelevancyUtil() {

    }

    /**
     * Compare two arrays modulo proof irrelevancy.
     *
     * @param a first array
     * @param b second array
     * @return whether they are equal (same length, equal elements)
     */
    public static <T> boolean compareImmutableArrays(
            ImmutableArray<T> a,
            ImmutableArray<T> b,
            BiPredicate<T, T> equalityPredicate) {
        if (a == b) {
            return true;
        }

        if (a.size() != b.size()) {
            return false;
        }

        for (int i = 0; i < b.size(); i++) {
            if (!equalityPredicate.test(b.get(i), a.get(i))) {
                return false;
            }
        }
        return true;
    }

    /**
     * Compute the hashcode of an iterable modulo proof irrelevancy.
     *
     * @param iter iterable of elements
     * @return combined hashcode
     */
    public static <T> int hashCodeIterable(Iterable<T> iter, ToIntFunction<T> hasher) {
        // adapted from Arrays.hashCode
        if (iter == null) {
            return 0;
        }

        int result = 1;

        for (T element : iter) {
            result = 31 * result + (element == null ? 0 : hasher.applyAsInt(element));
        }

        return result;
    }

    /**
     * Compare two immutable lists modulo proof irrelevancy.
     * A null list is considered equal to a zero-sized list.
     *
     * @param a first list
     * @param b second list
     * @return whether they are equal (same length, equal elements)
     */
    public static <T> boolean compareImmutableLists(
            ImmutableList<T> a, ImmutableList<T> b, BiPredicate<T, T> cmp) {
        if (a == b || (a == null && b.size() == 0) || (b == null && a.size() == 0)) {
            return true;
        }
        if (a == null || b == null || (a.size() != b.size())) {
            return false;
        }
        ImmutableList<T> remainderToCompare = a;
        while (!remainderToCompare.isEmpty()) {
            final T obj1 = remainderToCompare.head();
            if (!cmp.test(obj1, b.head())) {
                return false;
            }
            remainderToCompare = remainderToCompare.tail();
            b = b.tail();
        }
        return true;
    }

    /**
     * Compute the hashcode of an immutable list modulo proof irrelevancy.
     * implementation.
     *
     * @param list list of elements
     * @return combined hashcode
     */
    public static <T> int hashCodeImmutableList(
            ImmutableList<T> list, ToIntFunction<T> hasher) {
        if (list == null) {
            return 0;
        }
        var hashcode = Objects.hash(list.size());
        while (!list.isEmpty()) {
            if (list.head() != null) {
                hashcode = Objects.hash(hashcode, hasher.applyAsInt(list.head()));
            }
            list = list.tail();
        }
        return hashcode;
    }
}
