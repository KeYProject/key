/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.Objects;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

/**
 * Utility methods for the {@link EqualsModProofIrrelevancy} interface.
 *
 * @author Arne Keller
 */
public final class EqualsModProofIrrelevancyUtil {
    private EqualsModProofIrrelevancyUtil() {

    }

    /**
     * Compare two arrays using the elements' {@link EqualsModProofIrrelevancy} implementation.
     *
     * @param a first array
     * @param b second array
     * @return whether they are equal (same length, equal elements)
     */
    public static boolean compareArrays(EqualsModProofIrrelevancy[] a,
            EqualsModProofIrrelevancy[] b) {
        if (a == b) {
            return true;
        }

        if (a.length != b.length) {
            return false;
        }

        for (int i = 0; i < b.length; i++) {
            if (!(b[i]).equalsModProofIrrelevancy(a[i])) {
                return false;
            }
        }
        return true;
    }

    /**
     * Compare two arrays using the elements' {@link EqualsModProofIrrelevancy} implementation.
     *
     * @param a first array
     * @param b second array
     * @return whether they are equal (same length, equal elements)
     */
    public static boolean compareImmutableArrays(
            ImmutableArray<? extends EqualsModProofIrrelevancy> a,
            ImmutableArray<? extends EqualsModProofIrrelevancy> b) {
        if (a == b) {
            return true;
        }

        if (a.size() != b.size()) {
            return false;
        }

        for (int i = 0; i < b.size(); i++) {
            if (!(b.get(i)).equalsModProofIrrelevancy(a.get(i))) {
                return false;
            }
        }
        return true;
    }

    /**
     * Compute the hashcode of an iterable using the elements' {@link EqualsModProofIrrelevancy}
     * implementation.
     *
     * @param iter iterable of elements
     * @return combined hashcode
     */
    public static int hashCodeIterable(Iterable<? extends EqualsModProofIrrelevancy> iter) {
        // adapted from Arrays.hashCode
        if (iter == null) {
            return 0;
        }

        int result = 1;

        for (EqualsModProofIrrelevancy element : iter) {
            result = 31 * result + (element == null ? 0 : element.hashCodeModProofIrrelevancy());
        }

        return result;
    }

    /**
     * Compare two immutable lists using the elements' {@link EqualsModProofIrrelevancy}
     * implementation.
     * A null list is considered equal to a zero-sized list.
     *
     * @param a first list
     * @param b second list
     * @return whether they are equal (same length, equal elements)
     */
    public static boolean compareImmutableLists(
            ImmutableList<? extends EqualsModProofIrrelevancy> a,
            ImmutableList<? extends EqualsModProofIrrelevancy> b) {
        if (a == b || (a == null && b.size() == 0) || (b == null && a.size() == 0)) {
            return true;
        }
        if (a == null || b == null || (a.size() != b.size())) {
            return false;
        }
        ImmutableList<? extends EqualsModProofIrrelevancy> remainderToCompare = a;
        while (!remainderToCompare.isEmpty()) {
            EqualsModProofIrrelevancy obj1 = remainderToCompare.head();
            Object obj2 = b.head();
            if (!(obj1).equalsModProofIrrelevancy(obj2)) {
                return false;
            }
            remainderToCompare = remainderToCompare.tail();
            b = b.tail();
        }
        return true;
    }

    /**
     * Compute the hashcode of an immutable list using the elements'
     * {@link EqualsModProofIrrelevancy}
     * implementation.
     *
     * @param list list of elements
     * @return combined hashcode
     */
    public static int hashCodeImmutableList(
            ImmutableList<? extends EqualsModProofIrrelevancy> list) {
        if (list == null) {
            return 0;
        }
        var hashcode = Objects.hash(list.size());
        while (!list.isEmpty()) {
            if (list.head() != null) {
                hashcode = Objects.hash(hashcode,
                    (list.head()).hashCodeModProofIrrelevancy());
            }
            list = list.tail();
        }
        return hashcode;
    }
}
