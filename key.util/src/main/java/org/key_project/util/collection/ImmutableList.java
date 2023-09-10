/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collector;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;
import javax.annotation.Nonnull;

/**
 * List interface to be implemented by non-destructive lists
 */
public interface ImmutableList<T> extends Iterable<T>, java.io.Serializable {

    /**
     * Returns a Collector that accumulates the input elements into a new ImmutableList.
     *
     * @return a Collector that accumulates the input elements into a new ImmutableList.
     */
    static <T> Collector<T, List<T>, ImmutableList<T>> collector() {
        return Collector.of(LinkedList::new, List::add, (list1, list2) -> {
            list1.addAll(list2);
            return list1;
        }, ImmutableList::fromList);
    }

    /**
     * Creates an ImmutableList from a List.
     *
     * @param list a List.
     * @return an ImmutableList containing the same elements as the specified list.
     */
    static <T> ImmutableList<T> fromList(Collection<T> list) {
        ImmutableList<T> result = ImmutableSLList.nil();

        for (T el : list) {
            result = result.append(el);
        }

        return result;
    }

    /**
     * Return an empty immutable list.
     *
     * @return empty immutable list.
     * @param <T> the entry type of the list.
     */
    static <T> ImmutableList<T> of() {
        return ImmutableSLList.nil();
    }

    /**
     * Return a singleton immutable list.
     *
     * @param e1 the element to put into the list
     * @return singleton immutable list.
     * @param <T> the entry type of the list.
     */
    static <T> ImmutableList<T> of(T e1) {
        return ImmutableSLList.singleton(e1);
    }

    /**
     * Return an immutable list with two elements.
     * The iteration order is: e1 then e2
     *
     * @param e1 the element to put into the list
     * @param e2 the element to put into the list
     * @return (e1, e2) as immutable list
     * @param <T> the entry type of the list.
     */
    static <T> ImmutableList<T> of(T e1, T e2) {
        return ImmutableSLList.singleton(e2).prepend(e1);
    }

    /**
     * Return an immutable list with three elements.
     * The iteration order is: e1 then e2 then e3
     *
     * @param e1 the element to put into the list
     * @param e2 the element to put into the list
     * @param e3 the element to put into the list
     * @return (e1, e2, e3) as immutable list
     * @param <T> the entry type of the list.
     */
    static <T> ImmutableList<T> of(T e1, T e2, T e3) {
        return ImmutableSLList.singleton(e3).prepend(e2).prepend(e1);
    }

    /**
     * Return an immutable list with the iterated elements.
     * The iteration order is the order of the arguments
     *
     * @param es the elements to put into the list
     * @return (e1, e2, e3, ...) as immutable list
     * @param <T> the entry type of the list.
     */
    static <T> ImmutableList<T> of(T... es) {
        ImmutableList<T> result = ImmutableSLList.nil();
        for (int i = es.length - 1; i >= 0; i--) {
            result = result.prepend(es[i]);
        }
        return result;
    }

    /**
     * prepends element to the list (non-destructive)
     *
     * @param element the head of the created list
     * @return IList<T> with the new element as head and this list as tail
     */
    ImmutableList<T> prepend(T element);

    /**
     * prepends a whole list (non-destructive)
     *
     * @param list the list to be prepended
     * @return IList<T> list++this
     */

    ImmutableList<T> prepend(ImmutableList<T> list);

    /**
     * prepends an immutable list in reverse order, i.e., [4,5,6].prepend([1,2,3]) will be
     * [3,2,1,4,5,6] (more efficient than {@link ImmutableList#prepend(ImmutableList)})
     *
     * @return reverse(collection)++this
     */
    ImmutableList<T> prependReverse(ImmutableList<T> collection);

    /**
     * prepends an iterable collection in reverse order, i.e., [4,5,6].prepend([1,2,3]) will be
     * [3,2,1,4,5,6]
     *
     * @return reverse(collection)++this
     */
    ImmutableList<T> prependReverse(Iterable<T> collection);

    /**
     * prepends array (O(n))
     *
     * @param array the array of the elements to be prepended
     * @return IList<T> the new list
     */
    ImmutableList<T> prepend(@SuppressWarnings("unchecked") T... array);

    /**
     * appends element to the list (non-destructive)
     *
     * @param element to be added at the end
     * @return IList<T> with the new element at the end
     */
    ImmutableList<T> append(T element);

    /**
     * appends a whole list (non-destructive)
     *
     * @param list the list to be appended
     * @return IList<T> this++list
     */
    ImmutableList<T> append(ImmutableList<T> list);

    /**
     * appends an iterable collection
     */
    ImmutableList<T> append(Iterable<T> collection);

    /**
     * appends element at end (non-destructive) (O(n))
     *
     * @param array the array to be appended
     * @return IList<T> the new list
     */
    ImmutableList<T> append(@SuppressWarnings("unchecked") T... array);

    /**
     * @return <T> the first element in list
     */
    T head();

    /**
     * return true if predicate is fullfilled for at least one element
     *
     * @param predicate the predicate
     * @return true if predicate is fullfilled for at least one element
     */
    boolean exists(Predicate<T> predicate);

    /**
     * @return IList<T> tail of list
     */

    ImmutableList<T> tail();

    /**
     * @return IList<T> this list without the first <code>n</code> elements
     */
    ImmutableList<T> take(int n);

    /**
     * Reverses this list
     */
    ImmutableList<T> reverse();

    /**
     * @return Iterator<T> of this list
     */
    @Override
    Iterator<T> iterator();

    /**
     * @return boolean is true iff. obj is in List
     */
    boolean contains(T obj);

    /**
     * @return int representing number of elements in list
     */

    int size();

    /**
     * @return true iff the list is empty
     */
    boolean isEmpty();

    /**
     * removes first occurrence of obj
     *
     * @return new list
     */
    ImmutableList<T> removeFirst(T obj);

    /**
     * removes all occurrences of obj
     *
     * @return new list
     */
    ImmutableList<T> removeAll(T obj);

    /**
     * Convert the list to a Java array (O(n))
     */
    <S> S[] toArray(S[] array);

    /**
     * Convert the list to a Java array (O(n))
     */
    <S> S[] toArray(Class<S> type);


    /**
     * A stream object for this collection.
     *
     * @return a non-null stream object
     */
    default Stream<T> stream() {
        return StreamSupport.stream(this.spliterator(), false);
    }

    /**
     * Convert an {@link ImmutableList} to a {@link List}.
     *
     * @return This element converted to a {@link List}.
     */
    default List<T> toList() {
        List<T> result = new ArrayList<>();
        for (T t : this) {
            result.add(t);
        }
        return result;
    }

    /**
     * Returns an immutable list consisting of the elements of this list that match
     * the given predicate.
     *
     * @param predicate a non-interfering, stateless
     *        predicate to apply to each element to determine if it
     *        should be included
     *
     * @returns the filtered list
     */
    default @Nonnull ImmutableList<T> filter(@Nonnull Predicate<T> predicate) {
        return Immutables.filter(this, predicate);
    }

    /**
     * Returns an immutable list consisting of the results of applying the given
     * function to the elements of this list.
     *
     * @param <R> The element type of the result list
     * @param function a non-interfering, stateless function to apply to each element
     * @return the mapped list of the same length as this
     */
    default <R> ImmutableList<R> map(Function<T, R> function) {
        return Immutables.map(this, function);
    }

    /**
     * @param other prefix to check for
     * @return whether this list starts with the elements of the provided prefix
     */
    default boolean hasPrefix(ImmutableList<T> other) {
        if (other.size() > this.size()) {
            return false;
        }
        if (other.size() == 0) {
            return true;
        }
        if (Objects.equals(head(), other.head())) {
            return tail().hasPrefix(other.tail());
        } else {
            return false;
        }
    }

    /**
     * Remove a prefix from this list.
     *
     * @param prefix prefix to remove
     * @return new list with the prefix removed
     * @throws IllegalArgumentException if the provided prefix is not a prefix of this list
     */
    default ImmutableList<T> stripPrefix(ImmutableList<T> prefix) {
        if (prefix.isEmpty()) {
            return this;
        }
        if (!Objects.equals(head(), prefix.head())) {
            throw new IllegalArgumentException("not a prefix of this list");
        }
        return this.tail().stripPrefix(prefix.tail());
    }

    /**
     * Get the last element of this list.
     * Time complexity: O(n).
     *
     * @return last element of this list
     */
    default T last() {
        if (isEmpty()) {
            throw new IllegalStateException("last() called on empty list");
        }
        ImmutableList<T> remainder = this;
        while (!remainder.tail().isEmpty()) {
            remainder = remainder.tail();
        }
        return remainder.head();
    }

    /**
     * Get the n-th element of this list.
     *
     * @param idx the 0-based index of the element
     * @return the element at index idx.
     * @throws IndexOutOfBoundsException if idx is less than 0 or at
     *         least {@link #size()}.
     */
    default T get(int idx) {
        return take(idx).head();
    }

}
