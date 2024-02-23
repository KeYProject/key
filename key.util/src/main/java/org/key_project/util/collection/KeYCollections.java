/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * Utilities for Collections.
 *
 * @author Alexander Weigl
 * @version 1 (29.03.19)
 */
public class KeYCollections {
    // =======================================================
    // Methods operating on Arrays
    // =======================================================

    /**
     * Concatenates two arrays. The second array may have an entry type that is a subtype of the
     * first one.
     */
    public static <S, T extends S> S[] concat(S[] s1, T[] s2) {
        S[] res = Arrays.copyOf(s1, s1.length + s2.length);
        System.arraycopy(s2, 0, res, s1.length, s2.length);
        return res;
    }

    // =======================================================
    // Methods operating on Collections
    // =======================================================

    /**
     * Combine two maps by function application. Values of <code>m0</code> which are not keys of
     * <code>m1</code> are dropped. This implementation tries to use the same implementation of
     * {@link java.util.Map} (provided in Java SE) as <code>m0</code>.
     */
    public static <S, T, U> Map<S, U> apply(Map<S, ? extends T> m0, Map<T, U> m1) {
        Map<S, U> res;
        final int size = Math.min(m0.size(), m1.size());
        // try to use more specific implementation
        if (m0 instanceof java.util.TreeMap) {
            res = new java.util.TreeMap<>();
        } else if (m0 instanceof java.util.concurrent.ConcurrentHashMap) {
            res = new java.util.concurrent.ConcurrentHashMap<>(size);
        } else if (m0 instanceof java.util.IdentityHashMap) {
            res = new java.util.IdentityHashMap<>(size);
        } else if (m0 instanceof java.util.WeakHashMap) {
            res = new java.util.WeakHashMap<>(size);
        } else {
            res = new HashMap<>(size);
        }

        for (Map.Entry<S, ? extends T> e : m0.entrySet()) {
            final U value = m1.get(e.getValue());
            if (value != null) {
                res.put(e.getKey(), value);
            }
        }
        return res;
    }


    /**
     * Join the string representations of a collection of objects into onw string. The individual
     * elements are separated by a delimiter.
     * <p>
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection an arbitrary non-null collection
     * @param delimiter a non-null string which is put between the elements.
     * @return the concatenation of all string representations separated by the delimiter
     */
    public static String join(Iterable<?> collection, String delimiter) {
        return StreamSupport.stream(collection.spliterator(), false).map(Objects::toString)
                .collect(Collectors.joining(delimiter));
    }

    /**
     * Join the string representations of an array of objects into one string. The individual
     * elements are separated by a delimiter.
     * <p>
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection an arbitrary non-null array of objects
     * @param delimiter a non-null string which is put between the elements.
     * @return the concatenation of all string representations separated by the delimiter
     */
    public static String join(Object[] collection, String delimiter) {
        return Arrays.stream(collection).map(Objects::toString)
                .collect(Collectors.joining(delimiter));
    }

    /**
     * Takes a string and returns a string which is potentially shorter and contains a
     * sub-collection of the original characters.
     * <p>
     * All alphabetic characters (A-Z and a-z) are copied to the result while all other characters
     * are removed.
     *
     * @param string an arbitrary string
     * @return a string which is a sub-structure of the original character sequence
     * @author mattias ulbrich
     */
    public static /* @ non_null @ */ String filterAlphabetic(/* @ non_null @ */ String string) {
        StringBuilder res = new StringBuilder();
        for (int i = 0; i < string.length(); i++) {
            char c = string.charAt(i);
            if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')) {
                res.append(c);
            }
        }
        return res.toString();
    }

    /**
     * Creates a run-length encoding from the given positive integer array. The return array has the
     * following form:
     * every positive entry stands for its own. Every negative integer describes the repetition
     * of the following positive integer.
     * <p>
     * For example {@code [1, -5, 2, 1]} stands for {@code [1,2,2,2,2,2,1]}.
     *
     * @param array an integer array where
     */
    public static int[] runLengthEncoding(int[] array) {
        int len = array.length;
        int[] target = new int[2 * len];
        int used = 0;
        for (int i = 0; i < len; i++) {
            // Count occurrences of current character
            int count = 1;
            int symbol = array[i];
            while (i < len - 1 && symbol == array[i + 1]) {
                count++;
                i++;
            }
            if (count != 1) {
                target[used++] = -count;
            }
            target[used++] = symbol;
        }

        return Arrays.copyOf(target, used);
    }


    public static int[] runLengthEncoding(Collection<Integer> array) {
        var iter = array.iterator();
        class PushbackIterator implements Iterator<Integer> {
            private int pushedBack = -1;

            @Override
            public boolean hasNext() {
                return pushedBack >= 0 || iter.hasNext();
            }

            @Override
            public Integer next() {
                if (pushedBack >= 0) {
                    var v = pushedBack;
                    pushedBack = -1;
                    return v;
                }
                return iter.next();
            }

            public void pushBack(int last) {
                pushedBack = last;
            }
        }
        var piter = new PushbackIterator();
        int len = array.size();
        int[] target = new int[2 * len];
        int used = 0;

        while (piter.hasNext()) {
            // Count occurrences of current character
            int count = 1;
            int symbol = piter.next();
            int last = symbol;
            while (iter.hasNext() && (symbol == (last = piter.next()))) {
                count++;
            }
            if (last != symbol) {
                piter.pushBack(last);
            }
            if (count != 1) {
                target[used++] = -count;
            }
            target[used++] = symbol;
        }
        return Arrays.copyOf(target, used);
    }


    /**
     * Creates a lazy decoding for the given run-length encoding.
     */
    public static Iterator<Integer> runLengthDecoding(int[] rleArray) {
        return new Iterator<>() {
            int pos = 0;
            int count = 0;
            int value = -1;

            @Override
            public boolean hasNext() {
                return count > 0 || pos < rleArray.length;
            }

            @Override
            public Integer next() {
                if (count == 0) {
                    value = rleArray[pos++];
                    if (value < 0) {
                        count = (-value) - 1;
                        value = rleArray[pos++];
                    }
                } else {
                    count--;
                }
                return value;
            }
        };
    }
}
