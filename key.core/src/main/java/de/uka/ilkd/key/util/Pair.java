/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.Collection;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * Simple value object to hold two values.
 *
 * @param <T1> type of first element
 * @param <T2> type of second element
 */
public class Pair<T1, T2> {
    /**
     * First element.
     */
    public final T1 first;
    /**
     * Second element.
     */
    public final T2 second;


    /**
     * Construct a new pair containing the given values.
     *
     * @param first first element
     * @param second second element
     */
    public Pair(T1 first, T2 second) {
        this.first = first;
        this.second = second;
    }


    public String toString() {
        return "(" + first + ", " + second + ")";
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Pair<?, ?>)) {
            return false;
        }
        Pair<?, ?> p = (Pair<?, ?>) o;
        return Objects.equals(first, p.first) && Objects.equals(second, p.second);
    }


    @Override
    public int hashCode() {
        return Objects.hash(first, second);
    }

    ///////////////////////////////////////////////////////////
    // convenience methods to operate on collections of pairs

    /**
     * Convert a collection of pairs into a map.
     *
     * @throws IllegalArgumentException if it contains duplicate first entries
     */
    public static <S, T> Map<S, T> toMap(Collection<Pair<S, T>> pairs) {
        Map<S, T> res = new java.util.LinkedHashMap<>();
        for (Pair<S, T> p : pairs) {
            if (res.containsKey(p.first)) {
                throw new IllegalArgumentException(
                    "Cannot covert " + pairs + " into a map; it contains duplicate first entries.");
            }
            res.put(p.first, p.second);
        }
        return res;
    }

    /**
     * Returns the set of first entries from a collection of pairs.
     */
    public static <S, T> Set<S> getFirstSet(Collection<Pair<S, T>> pairs) {
        Set<S> res = new java.util.HashSet<>();
        for (Pair<S, T> p : pairs) {
            res.add(p.first);
        }
        return res;
    }

    /**
     * Returns the set of second entries from a collection of pairs.
     */
    public static <S, T> Set<T> getSecondSet(Collection<Pair<S, T>> pairs) {
        Set<T> res = new java.util.HashSet<>();
        for (Pair<S, T> p : pairs) {
            res.add(p.second);
        }
        return res;
    }
}
