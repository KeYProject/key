/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;


import java.util.Objects;

/**
 * Simple value object to hold three values.
 *
 * @param <T1> type of first element
 * @param <T2> type of second element
 * @param <T3> type of third element
 */
public class Triple<T1, T2, T3> {
    /**
     * First element.
     */
    public final T1 first;
    /**
     * Second element.
     */
    public final T2 second;
    /**
     * Third element.
     */
    public final T3 third;


    /**
     * Construct a new triple containing the provided values.
     *
     * @param first first element
     * @param second second element
     * @param third third element
     */
    public Triple(T1 first, T2 second, T3 third) {
        this.first = first;
        this.second = second;
        this.third = third;
    }


    public String toString() {
        return "(" + first + ", " + second + ", " + third + ")";
    }


    public boolean equals(Object o) {
        if (!(o instanceof Triple<?, ?, ?>)) {
            return false;
        }
        Triple<?, ?, ?> p = (Triple<?, ?, ?>) o;
        return Objects.equals(first, p.first) && Objects.equals(second, p.second)
                && Objects.equals(third, p.third);
    }


    public int hashCode() {
        return Objects.hash(first, second, third);
    }
}
