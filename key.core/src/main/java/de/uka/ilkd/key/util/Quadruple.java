/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.Objects;

/**
 * Simple 4-tuple data object.
 *
 * @param <T1> type of first element
 * @param <T2> type of second element
 * @param <T3> type of third element
 * @param <T4> type of fourth element
 * @author Dominic Scheurer
 */
public class Quadruple<T1, T2, T3, T4> implements Comparable<Quadruple<T1, T2, T3, T4>> {
    public final T1 first;
    public final T2 second;
    public final T3 third;
    public final T4 fourth;


    public Quadruple(T1 first, T2 second, T3 third, T4 fourth) {
        this.first = first;
        this.second = second;
        this.third = third;
        this.fourth = fourth;
    }


    public String toString() {
        return "(" + first + ", " + second + ", " + third + ", " + fourth + ")";
    }


    public boolean equals(Object o) {
        if (!(o instanceof Quadruple<?, ?, ?, ?>)) {
            return false;
        }
        Quadruple<?, ?, ?, ?> p = (Quadruple<?, ?, ?, ?>) o;
        return (Objects.equals(first, p.first))
                && (Objects.equals(second, p.second))
                && (Objects.equals(third, p.third))
                && (Objects.equals(fourth, p.fourth));
    }


    public int hashCode() {
        int res = 0;
        if (first != null) {
            res += 666 * first.hashCode();
        }
        if (second != null) {
            res += 42 * second.hashCode();
        }
        if (third != null) {
            res += 23 * third.hashCode();
        }
        if (fourth != null) {
            res += 37 * fourth.hashCode();
        }
        return res;
    }

    @Override
    public int compareTo(Quadruple<T1, T2, T3, T4> o) {
        if (first instanceof Comparable) {
            int r1 = ((Comparable<T1>) first).compareTo(o.first);
            if (r1 != 0) {
                return r1;
            }
        }
        if (second instanceof Comparable) {
            int r1 = ((Comparable<T2>) second).compareTo(o.second);
            if (r1 != 0) {
                return r1;
            }
        }
        if (third instanceof Comparable) {
            int r1 = ((Comparable<T3>) third).compareTo(o.third);
            if (r1 != 0) {
                return r1;
            }
        }
        if (fourth instanceof Comparable) {
            int r1 = ((Comparable<T4>) fourth).compareTo(o.fourth);
            if (r1 != 0) {
                return r1;
            }
        }
        return 0;
    }
}
