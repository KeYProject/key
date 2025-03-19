/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.Comparator;

/**
 * Simple 4-tuple data object.
 *
 * @param <T1> type of first element
 * @param <T2> type of second element
 * @param <T3> type of third element
 * @param <T4> type of fourth element
 * @author Dominic Scheurer
 */
public record Quadruple<T1, T2, T3, T4>(T1 first, T2 second, T3 third, T4 fourth) {

    /**
     * Constructs a comparator for a {@link Quadruple} with arbitrary comparable arguments.
     */
    public static <T1 extends Comparable<T1>, T2 extends Comparable<T2>,
            T3 extends Comparable<T3>, T4 extends Comparable<T4>>
    Comparator<Quadruple<T1, T2, T3, T4>> getComparator() {
        Comparator<Quadruple<T1, T2, T3, T4>> t1 = Comparator.comparing(it -> it.first);
        Comparator<Quadruple<T1, T2, T3, T4>> t2 = Comparator.comparing(it -> it.second);
        Comparator<Quadruple<T1, T2, T3, T4>> t3 = Comparator.comparing(it -> it.third);
        Comparator<Quadruple<T1, T2, T3, T4>> t4 = Comparator.comparing(it -> it.fourth);
        return t1.thenComparing(t2).thenComparing(t3).thenComparing(t4);
    }

    public String toString() {
        return "(" + first + ", " + second + ", " + third + ", " + fourth + ")";
    }
}
