/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collector;
import java.util.stream.Collector.Characteristics;
import java.util.stream.Stream;
import javax.annotation.Nonnull;

/**
 * interface implemented by non-destructive Sets. CONVENTION: Each SetOf<T> implementation has to
 * offer a public static final variable .<called>nil()
 */

public interface ImmutableSet<T> extends Iterable<T>, java.io.Serializable {

    /**
     * Returns a Collector that accumulates the input elements into a new ImmutableSet.
     *
     * @return a Collector that accumulates the input elements into a new ImmutableSet.
     */
    static <T> Collector<T, Set<T>, ImmutableSet<T>> collector() {
        return Collector.of(HashSet::new, Set::add, (set1, set2) -> {
            set1.addAll(set2);
            return set1;
        }, ImmutableSet::fromSet, Characteristics.UNORDERED);
    }

    /**
     * Creates an ImmutableSet from a Set.
     *
     * @param set a Set.
     * @return an ImmutableSet containing the same elements as the specified set.
     */
    static <T> ImmutableSet<T> fromSet(Set<T> set) {
        ImmutableSet<T> result = DefaultImmutableSet.nil();

        for (T el : set) {
            result = result.add(el);
        }

        return result;
    }

    /**
     * Builds a single set with the given obj.
     */
    static <T> ImmutableSet<T> singleton(T obj) {
        ImmutableSet<T> result = DefaultImmutableSet.nil();
        return result.add(obj);
    }

    static <T> ImmutableSet<T> empty() {
        return DefaultImmutableSet.nil();
    }


    static <T> ImmutableSet<T> fromCollection(@Nonnull Collection<? extends T> seq) {
        return fromSet(new HashSet<>(seq));
    }

    /**
     * @return a {@code Set} containing the same elements as this {@code ImmutableSet}
     */
    Set<T> toSet();

    /**
     * Adds an element
     *
     * @return a set containing all elements of this one and the specified element.
     */
    ImmutableSet<T> add(T element);

    /** @return union of this set with set */
    ImmutableSet<T> union(ImmutableSet<? extends T> set);

    /** @return intersection of this set with set */
    ImmutableSet<T> intersect(ImmutableSet<? extends T> set);

    /** @return Iterator<T> of the set */
    @Override
    Iterator<T> iterator();

    /** @return Stream<T> of the set */
    Stream<T> stream();

    /**
     * return true if predicate is fullfilled for at least one element
     *
     * @param predicate the predicate
     * @return true if predicate is fullfilled for at least one element
     */
    boolean exists(Predicate<T> predicate);

    /** @return true iff obj in set */
    boolean contains(T obj);

    /** @return true iff this set is subset of set s */
    boolean subset(ImmutableSet<T> s);

    /** @return int the cardinality of the set */
    int size();

    /** @return true iff the set is empty */
    boolean isEmpty();

    /** @return set without element */
    ImmutableSet<T> remove(T element);

    /**
     * @return true iff the this set is subset of o and vice versa.
     */
    @Override
    boolean equals(Object o);

    @Override
    int hashCode();

    /**
     * adds an element, barfs if the element is already present
     *
     * @param element of type <T> that has to be added to this set
     * @throws NotUniqueException if the element is already present
     */
    ImmutableSet<T> addUnique(T element) throws NotUniqueException;

    /**
     * Convert the set to a Java array
     */
    <S> S[] toArray(S[] array);

    default ImmutableSet<T> add(Iterable<T> seq) {
        ImmutableSet<T> cur = this;
        for (T item : seq) {
            cur = cur.add(item);
        }
        return cur;
    }
}
