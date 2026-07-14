/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.lang.reflect.Array;
import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import org.jspecify.annotations.Nullable;

/// List interface to be implemented by non-destructive immutable lists.
///
/// This interface provides a functional, immutable alternative to [java.util.List].
/// All operations that would modify a list instead return new [ImmutableList] instances,
/// preserving the original list unchanged. Operations are optimized for performance, typically
/// achieving `O(1)` complexity by constructing views of the original list rather than
/// copying data.
///
/// ## Key Features
///
/// - **Immutability:** Once created, lists cannot be modified
/// - **Structural sharing:** New lists share structure with existing lists when possible
/// - **Lazily evaluated views:** Operations like [#reverse()], [#skip(int)],
/// and [#take(int)] create views without copying elements
///
/// ## Factory Methods
///
/// Use the static factory methods to create instances:
///
/// - [#of()] - empty list
/// - [#of(Object)] - singleton list
/// - [#of(Object...)] - list from varargs
/// - [#fromList(List)] - list from Java List
/// - [#fromArray(Object\[\])] - list from array
///
/// @param <T> the type of elements in this list (may be nullable)
/// @see ImmutableListSubList view of a sub-list
/// @see ImmutableListArray base implementation using arrays
/// @see ImmutableListConcat concatenated view of two lists
/// @see ImmutableListReverse reverse view of a list
/// @see ImmutableListList base implementation using java.util.List
/// @see ImmutableSLList base implementation using cons/nil structure
@SuppressWarnings("unchecked")
public interface ImmutableList<T extends @Nullable Object>
        extends Iterable<T>, java.io.Serializable {

    /// Returns a [Collector] that accumulates the input elements into a new [ImmutableList]
    /// using a [LinkedList]. If you know the capacity in advance, use [#collector(int)]
    @SuppressWarnings("nullness") // it seems some annotations are missing on Collector.of ...
    static <T extends @Nullable Object> Collector<T, List<T>, ImmutableList<T>> collector() {
        return Collector.of(LinkedList::new, List::add, (list1, list2) -> {
            list1.addAll(list2);
            return list1;
        }, ImmutableListList::createDirectlyWithoutImmutableGuarantee);
    }

    /// Returns a [Collector] that accumulates the input elements into a new [ImmutableList].
    ///
    /// @param initialCapacity the initial capacity of the [ArrayList] used to collect the elements
    @SuppressWarnings("nullness")
    static <T extends @Nullable Object> Collector<T, List<T>, ImmutableList<T>> collector(
            int initialCapacity) {
        return Collector.of(() -> new ArrayList<>(initialCapacity), List::add, (list1, list2) -> {
            list1.addAll(list2);
            return list1;
        }, ImmutableListList::createDirectlyWithoutImmutableGuarantee);
    }

    /// Creates an [ImmutableList] from an [Iterable].
    ///
    /// This method is not recommended for use as space overhead is required.
    /// Prefer [#fromList(List)] or [#fromArray(Object\[\])] when possible,
    /// as [Iterable] have an unknown size.
    ///
    /// This method is idempotent, if `list` is an [ImmutableList].
    ///
    /// @param list an Iterable to convert
    /// @param <T> the element type
    /// @return an ImmutableList containing the same elements as the specified iterable
    /// @see #fromList(List)
    /// @see #fromArray(Object[])
    static <T extends @Nullable Object> ImmutableList<T> fromList(Iterable<? extends T> list) {
        // Short-cuts, iterables are often lists, if so use them and try to avoid copy.
        if (list instanceof ImmutableList<?> ilist) {
            return (ImmutableList<T>) ilist;
        }

        if (list instanceof List<?> ilist) {
            return fromList((List<T>) ilist);
        }

        List<T> seq = new ArrayList<>(64);
        for (var t : list) {
            seq.add(t);
        }
        return fromList(seq);
    }

    /// Creates an [ImmutableList] from a [List].
    ///
    /// This method wraps the given list in an immutable wrapper. The input list is
    /// copied to ensure immutability guarantees are maintained.
    ///
    /// @param <T> the element type
    /// @param list the list to wrap
    /// @return an ImmutableList containing the elements of the input list
    static <T extends @Nullable Object> ImmutableList<T> fromList(List<T> list) {
        return new ImmutableListList<>(list);
    }

    /// Creates an [ImmutableList] from an array.
    ///
    /// This method wraps the given array in an immutable wrapper. The input array is
    /// copied to ensure immutability guarantees are maintained.
    ///
    /// @param <T> the element type
    /// @param array the array to wrap
    /// @return an ImmutableList containing the elements of the input array
    static <T extends @Nullable Object> ImmutableList<T> fromArray(T[] array) {
        return new ImmutableListArray<>(array);
    }


    /// Return an empty immutable list.
    ///
    /// @param <T> the entry type of the list.
    /// @return empty immutable list.
    static <T extends @Nullable Object> ImmutableList<T> of() {
        return nil();
    }

    /// Return a singleton immutable list.
    ///
    /// @param e1 the element to put into the list
    /// @param <T> the entry type of the list.
    /// @return singleton immutable list.
    static <T extends @Nullable Object> ImmutableList<T> of(T e1) {
        return singleton(e1);
    }

    /// Return an immutable list with the iterated elements.
    /// The iteration order is the order of the arguments.
    ///
    /// Optimization for `n=0` and `n=1`.
    ///
    /// @param es the elements to put into the list
    /// @param <T> the entry type of the list.
    /// @return (e1, e2, e3, ...) as immutable list
    static <T extends @Nullable Object> ImmutableList<T> of(T... es) {
        if (es.length == 0) {
            return of();
        }

        if (es.length == 1) {
            return of(es[0]);
        }

        return new ImmutableListArray<>(es);
    }

    /// the empty list
    static <T extends @Nullable Object> ImmutableList<T> nil() {
        return (ImmutableSLList<T>) ImmutableSLList.NIL.NIL;
    }

    /// Creates an [ImmutableList] containing a single element.
    ///
    /// @param <T> the element type
    /// @param obj the element to put in the list
    /// @return a singleton list containing only the specified element
    static <T extends @Nullable Object> ImmutableList<T> singleton(T obj) {
        return new ImmutableSLList.Cons<>(obj, nil());
    }

    /// Returns a string representation of the given immutable list.
    ///
    /// The string representation consists of the elements enclosed in square brackets,
    /// separated by ", ".
    ///
    /// @param <T> the element type
    /// @param seq the list to convert to string
    /// @return a string representation in the format "[e1, e2, ..., en]"
    static <T extends @Nullable Object> String toString(ImmutableList<T> seq) {
        return seq.stream().map(Objects::toString).collect(Collectors.joining(", ", "[", "]"));
    }

    /// Computes a hash code for the given immutable list.
    ///
    /// The hash code is computed by iterating over all elements and combining
    /// their hash codes using the formula: `hash = 31 * hash + elementHash`.
    /// Null elements contribute 0 to the hash.
    ///
    /// @param <T> the element type
    /// @param seq the list to compute hash for (may be null)
    /// @return the hash code of the list, or 0 if the list is null
    static <T extends @Nullable Object> int hash(@Nullable ImmutableList<T> seq) {
        int hash = 0;
        if (seq != null) {
            for (var e : seq) {
                hash = 31 * hash + (e == null ? 0 : e.hashCode());
            }
        }
        return hash;
    }

    /// Prepends a single element to this list.
    ///
    /// @param element the element to prepend
    /// @return a new list with the element at the beginning
    default ImmutableList<T> prepend(T element) {
        return new ImmutableListConcat<>(ImmutableList.singleton(element), this);
    }

    /// Prepends another list to this list.
    ///
    /// @param list the list to prepend
    /// @return a new list with the given list's elements at the beginning
    default ImmutableList<T> prepend(ImmutableList<T> list) {
        return new ImmutableListConcat<>(list, this);
    }

    /// Prepends a reversed collection to this list.
    ///
    /// @param collection the collection to reverse and prepend
    /// @return a new list with the reversed collection's elements at the beginning
    default ImmutableList<T> prependReverse(ImmutableList<T> collection) {
        return new ImmutableListConcat<>(collection.reverse(), this);
    }

    /// Prepends a reversed iterable to this list.
    ///
    /// @param collection the iterable to reverse and prepend
    /// @return a new list with the reversed iterable's elements at the beginning
    default ImmutableList<T> prependReverse(Iterable<T> collection) {
        return new ImmutableListConcat<>(ImmutableList.fromList(collection).reverse(), this);
    }

    /// Prepends an array to this list.
    ///
    /// @param array the array to prepend
    /// @return a new list with the array's elements at the beginning
    default ImmutableList<T> prepend(T... array) {
        return new ImmutableListConcat<>(ImmutableList.fromArray(array), this);
    }

    /// Appends a single element to this list.
    ///
    /// @param element the element to append
    /// @return a new list with the element at the end
    default ImmutableList<T> append(T element) {
        return new ImmutableListConcat<>(this, of(element));
    }

    /// Appends another list to this list.
    ///
    /// @param list the list to append
    /// @return a new list with the given list's elements at the end
    default ImmutableList<T> append(ImmutableList<T> list) {
        return new ImmutableListConcat<>(this, list);
    }

    /// Appends an iterable collection to this list.
    ///
    /// @param collection the iterable to append
    /// @return a new list with the iterable's elements at the end
    default ImmutableList<T> append(Iterable<T> collection) {
        return new ImmutableListConcat<>(this, ImmutableList.fromList(collection));
    }

    /// Appends an array to this list (non-destructive) in O(1).
    ///
    /// @param array the array to append
    /// @return a new list with the array's elements at the end
    default ImmutableList<T> append(T... array) {
        return new ImmutableListConcat<>(this, ImmutableList.fromArray(array));
    }

    /// Returns the first element of this list.
    ///
    /// @return the first element in the list
    default T head() {
        return get(0);
    }

    /// Returns true if the predicate is fulfilled for at least one element.
    ///
    /// The default implementation is based on the [#stream()] functionality.
    ///
    /// @param predicate the predicate to test
    /// @return true if predicate is fulfilled for at least one element
    /// @see #stream()
    /// @see #spliterator()
    default boolean exists(Predicate<? super T> predicate) {
        return stream().anyMatch(predicate);
    }

    /// Returns the list without its head element.
    ///
    /// @return a new list without the first element
    /// @see #skip(int)
    default ImmutableList<T> tail() {
        return skip(1);
    }

    /// Returns the list without the first `n` elements.
    ///
    /// The default implementation takes `O(1)` time and avoids copying
    /// the underlying data structure by creating a view.
    ///
    /// For any integer `k`, the following invariant holds:
    /// `concat(seq.take(k), seq.skip(k)) == seq`
    ///
    /// @param n the number of elements to skip
    /// @return a new list without the first n elements
    /// @see #take(int)
    /// @see ImmutableListSubList
    default ImmutableList<T> skip(int n) {
        return new ImmutableListSubList<>(this, n);
    }

    /// Returns a list containing the first `n` elements.
    ///
    /// The default implementation takes `O(1)` time and avoids copying
    /// the underlying data structure by creating a view.
    ///
    /// @param n the number of elements to take
    /// @return a new list containing the first n elements
    /// @see #skip(int)
    /// @see ImmutableListSubList
    default ImmutableList<T> take(int n) {
        if (n == 0) {
            return nil();
        }
        return new ImmutableListSubList<>(this, 0, n);
    }

    /// Returns a reversed view of this list.
    ///
    /// @return a new list with elements in reverse order
    default ImmutableList<T> reverse() {
        return new ImmutableListReverse<>(this);
    }

    /// Returns an [Iterator] walking through the elements by
    /// increasing position.
    ///
    /// The default implementation uses an iterator based on [#get(int)] and [#size()].
    ///
    /// @return Iterator of this list
    @Override
    default Iterator<T> iterator() {
        return new Iterator<>() {
            int cursor = 0;

            @Override
            public boolean hasNext() {
                return cursor < size();
            }

            @Override
            public T next() {
                return get(cursor++);
            }
        };
    }

    /// Checks if this list contains the specified element.
    ///
    /// @param obj the element to search for
    /// @return true if and only if obj is in this list
    default boolean contains(@Nullable Object obj) {
        return exists(it -> Objects.equals(obj, it));
    }

    /// Returns the number of elements in this list.
    ///
    /// @return int representing number of elements in list
    int size();

    /// Checks if this list is empty.
    ///
    /// @return true if and only if the list is empty
    boolean isEmpty();

    /// Removes the first occurrence of the specified element from this list.
    ///
    /// @param obj the element to remove
    /// @return a new list with the first occurrence of obj removed
    ImmutableList<T> removeFirst(T obj);

    /// Removes all occurrences of the specified element from this list.
    ///
    /// @param obj the element to remove
    /// @return a new list with all occurrences of obj removed
    ImmutableList<T> removeAll(T obj);

    /// Converts the list to a Java array in `O(n)` time based on the
    /// [#iterator()] implementation.
    ///
    /// If you can convert faster, feel free to override this method.
    ///
    /// @param <S> the component type of the array
    /// @param array the array into which to store the elements, or used for type hint
    /// @return an array containing all elements in this list
    /// @see #iterator()
    @SuppressWarnings("unchecked")
    default <S extends @Nullable Object> S[] toArray(S[] array) {
        S[] result;
        if (array.length < size()) {
            Class<? extends Object[]> arrayClass = array.getClass();
            assert arrayClass.isArray()
                    : "@AssumeAssertion(nullness): This has indeed a component type";
            result = (S[]) Array.newInstance(arrayClass.getComponentType(), size());
        } else {
            result = array;
        }

        int pos = 0;
        for (var item : this) {
            result[pos++] = (S) item;
        }
        return result;
    }

    /// Converts the list to a Java array in `O(n)` time using the given component type.
    ///
    /// @param <S> the component type of the array
    /// @param type the class of the type
    /// @return an array of the specified type containing all elements in this list
    /// @see #iterator()
    default <S extends @Nullable Object> S[] toArray(Class<S> type) {
        S[] result = (S[]) Array.newInstance(type, size());
        int pos = 0;
        for (var head : this) {
            // Somehow the nullness checker needs this cast to be explicit.
            result[pos++] = (S) type.cast(head);
        }
        return result;
    }


    /// A stream object for this collection containing all elements of this collection.
    ///
    /// @return a non-null stream object
    /// @see #spliterator()
    /// @see #iterator()
    default Stream<T> stream() {
        return StreamSupport.stream(this.spliterator(), false);
    }

    /// Convert an [ImmutableList] to a [List].
    ///
    /// @return This element converted to a [List].
    default List<T> toList() {
        List<T> result = new ArrayList<>();
        for (T t : this) {
            result.add(t);
        }
        return result;
    }

    /// Returns an immutable list consisting of the elements of this list that match
    /// the given predicate.
    ///
    /// @param predicate a non-interfering, stateless
    /// predicate to apply to each element to determine if it
    /// should be included
    /// @return the filtered list
    default ImmutableList<T> filter(Predicate<? super T> predicate) {
        return Immutables.filter(this, predicate);
    }

    /// Returns an immutable list consisting of the results of applying the given
    /// function to the elements of this list.
    ///
    /// @param <R> The element type of the result list
    /// @param function a non-interfering, stateless function to apply to each element
    /// @return the mapped list of the same length as this
    default <R extends @Nullable Object> ImmutableList<R> map(Function<? super T, R> function) {
        return Immutables.map(this, function);
    }

    /// Returns whether this list starts with the elements of the provided prefix.
    ///
    /// The current implementation is not good, using recursion.
    ///
    /// @param other prefix to check for
    default boolean hasPrefix(ImmutableList<? extends T> other) {
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

    /// Remove a prefix from this list.
    ///
    /// @param prefix prefix to remove
    /// @return new list with the prefix removed
    /// @throws IllegalArgumentException if the provided prefix is not a prefix of this list
    default ImmutableList<T> stripPrefix(ImmutableList<? extends T> prefix) {
        if (prefix.isEmpty()) {
            return this;
        }
        if (!Objects.equals(head(), prefix.head())) {
            throw new IllegalArgumentException("not a prefix of this list");
        }
        return this.tail().stripPrefix(prefix.tail());
    }

    /// Get the last element of this list.
    /// The time complexity differs, for {@link ImmutableList} and {@link ImmutableListArray} it is
    /// in `O(1)`;
    /// for {@link ImmutableSLList} in `O(n)`.
    ///
    /// @return last element of this list
    default T last() throws NoSuchElementException {
        if (isEmpty()) {
            throw new NoSuchElementException("last() called on empty list");
        }
        return get(size() - 1);
    }

    /// Get the n-th element of this list.
    ///
    /// @param idx the 0-based index of the element
    /// @return the element at index idx.
    /// @throws IndexOutOfBoundsException if idx is less than 0 or at least [#size()].
    T get(int idx);

    /// Compares two [ImmutableList] instances for content equality.
    ///
    /// Two lists are considered equal if they have the same size and contain
    /// equal elements at corresponding positions.
    ///
    /// @param seq1 the first list to compare
    /// @param seq2 the second list to compare
    /// @return true if both lists contain the same elements in the same order
    static boolean equals(ImmutableList<?> seq1, ImmutableList<?> seq2) {
        final var size = seq1.size();
        if (size == seq2.size()) {
            for (int i = 0; i < size; i++) {
                if (!Objects.equals(seq1.get(i), seq2.get(i))) {
                    return false;
                }
            }
            return true;
        }
        return false;
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
