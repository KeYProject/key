/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * This class is a collection of methods that operate on immutable collections, in particular
 * {@link ImmutableSet}s and {@link ImmutableList}s.
 *
 * This class cannot be instantiated.
 *
 * @author Mattias Ulbrich
 */
public final class Immutables {

    private Immutables() {
        throw new Error();
    }

    /**
     * Checks whether an immutable list is free of duplicates.
     *
     * A list has a duplicate if it during iteration it visits two objects o1 and o2 such that
     * <code>o1==null ? o2 == null : o1.equals(o2)</code> is true. <code>null</code> may appear in
     * the list.
     *
     * The implementation uses a hash set internally and thus runs in O(n).
     *
     * @param list any list, must not be <code>null</code>
     * @return true iff every
     */
    public static <T> boolean isDuplicateFree(ImmutableList<T> list) {

        HashSet<T> set = new HashSet<>();
        for (T element : list) {
            if (set.contains(element)) {
                return false;
            }
            set.add(element);
        }

        return true;
    }

    /**
     * Removes duplicate entries from an immutable list.
     *
     * A list has a duplicate if it during iteration it visits two objects o1 and o2 such that
     * <code>o1==null ? o2 == null : o1.equals(o2)</code> is true. <code>null</code> may appear in
     * the list.
     *
     * If an element occurs duplicated, its first (in order of iteration) occurrence is kept, while
     * later occurrences are removeed.
     *
     * If a list iterates "a", "b", "a" in this order, removeDuplicates returns a list iterating
     * "a", "b".
     *
     * The implementation uses a hash set internally and thus runs in O(n).
     *
     * It reuses as much created datastructure as possible. In particular, if the list is already
     * duplicate-fre, it does not allocate new memory (well, only temporarily) and returns the
     * argument.
     *
     * Sidenote: Would that not make a nice KeY-Verification condition? Eat your own dogfood.
     *
     * @param list any list, must not be <code>null</code>
     *
     * @return a duplicate-free version of the argument, never <code>null</code>
     */
    public static <T> ImmutableList<T> removeDuplicates(ImmutableList<T> list) {

        if (list.isEmpty()) {
            return list;
        }

        ImmutableList<ImmutableList<T>> stack = ImmutableSLList.nil();

        while (!list.isEmpty()) {
            stack = stack.prepend(list);
            list = list.tail();
        }

        HashSet<T> alreadySeen = new HashSet<>();
        ImmutableList<T> result = ImmutableSLList.nil();

        while (!stack.isEmpty()) {
            ImmutableList<T> top = stack.head();
            T element = top.head();
            stack = stack.tail();
            if (alreadySeen.contains(element)) {
                // ok, no more reuse possible, go to 2nd loop
                break;
            }
            result = top;
            alreadySeen.add(element);
        }

        while (!stack.isEmpty()) {
            ImmutableList<T> top = stack.head();
            T element = top.head();
            stack = stack.tail();
            if (!alreadySeen.contains(element)) {
                result = result.prepend(element);
                alreadySeen.add(element);
            }
        }

        return result;

    }

    public static <T> ImmutableList<T> concatDuplicateFreeLists(ImmutableList<T> l1,
            ImmutableList<? extends T> l2) {

        Set<T> lookup = new HashSet<>();
        for (T element : l1) {
            lookup.add(element);
        }

        ImmutableList<T> result = l1;
        for (T element : l2) {
            if (!lookup.contains(element)) {
                result = result.prepend(element);
            }
        }

        return result;
    }

    public static <T> ImmutableSet<T> createSetFrom(Iterable<T> iterable) {
        return DefaultImmutableSet.fromImmutableList(createListFrom(iterable));
    }

    /**
     * Returns an immutable list consisting of the elements of the
     * given iterable collection.
     *
     * The iteration order of the result is identical to that of the argument.
     *
     * @param iterable the collection to iterate through to obtain the elements
     *        for the resulting list
     *
     * @returns the view onto the iterable as an immutable list
     */
    public static <T> ImmutableList<T> createListFrom(Iterable<T> iterable) {
        ImmutableList<T> result = ImmutableSLList.nil();
        for (T t : iterable) {
            result = result.prepend(t);
        }
        return result.reverse();
    }

    /**
     * Returns an immutable list consisting of the elements of the list that match
     * the given predicate.
     *
     * @param ts non-null immutable list.
     *
     * @param predicate a non-interfering, stateless
     *        predicate to apply to each element to determine if it
     *        should be included
     *
     * @returns the filtered list
     */
    public static <T> ImmutableList<T> filter(ImmutableList<T> ts, Predicate<T> predicate) {
        // This must be a loop. A tail recursive implementation is not optimised
        // by the compiler and quickly leads to a stack overlow.
        ImmutableList<T> acc = ImmutableSLList.nil();
        while (ts.size() > 0) {
            T hd = ts.head();
            if (predicate.test(hd)) {
                acc = acc.prepend(hd);
            }
            ts = ts.tail();
        }
        return acc.reverse();
    }

    /**
     * Returns an immutable list consisting of the results of applying the given
     * function to the elements of the list.
     *
     * @param <R> The element type of the result list
     * @param ts ts non-null immutable list.
     * @param function a non-interfering, stateless function to apply to each element
     * @return the mapped list of the same length as this
     */
    public static <T, R> ImmutableList<R> map(ImmutableList<T> ts, Function<T, R> function) {
        // This must be a loop. A tail recursive implementation is not optimised
        // by the compiler and quickly leads to a stack overlow.
        ImmutableList<R> acc = ImmutableSLList.nil();
        while (ts.size() > 0) {
            T hd = ts.head();
            acc = acc.prepend(function.apply(hd));
            ts = ts.tail();
        }
        return acc.reverse();
    }
}
