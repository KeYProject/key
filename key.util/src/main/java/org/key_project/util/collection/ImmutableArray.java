/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.lang.reflect.Array;
import java.util.*;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import org.key_project.util.Strings;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class ImmutableArray<S extends @Nullable Object>
        implements java.lang.Iterable<S>, java.io.Serializable {

    private static final long serialVersionUID = -9041545065066866250L;

    private final S[] content;

    /**
     * creates an empty new <S>Array
     */
    @SuppressWarnings("unchecked")
    public ImmutableArray() {
        content = (S[]) new Object[0];
    }

    /**
     * creates a new <S>Array
     *
     * @param arr the ProgrammElement array to wrap
     */
    @SuppressWarnings("unchecked")
    public ImmutableArray(S... arr) {
        this(arr, 0, arr.length);
    }

    @SuppressWarnings("unchecked")
    public ImmutableArray(S[] arr, int lower, int upper) {
        Class<? extends Object[]> arrayClass = arr.getClass();
        assert arrayClass.isArray() : "@AssumeAssertion(nullness): arrayClass is an array";
        content = (S[]) Array.newInstance(arrayClass.getComponentType(), upper - lower);
        System.arraycopy(arr, lower, content, 0, upper - lower);
    }

    /**
     * <p>
     * creates a new immutable array with the contents of the given collection.
     * </p>
     * <p>
     * The order of elements is defined by the collection.
     * </p>
     *
     * @param list a non-null collection (order is preserved)
     */
    @SuppressWarnings("unchecked")
    public ImmutableArray(@NonNull Collection<? extends S> list) {
        content = (S[]) list.toArray();
    }

    /**
     * gets the element at the specified position
     *
     * @param pos an int describing the position
     * @return the element at pos
     */
    public final S get(int pos) {
        return content[pos];
    }

    /**
     * returns the last element of the array
     *
     * @return the element at position size() - 1
     */
    public final S last() {
        return content[content.length - 1];
    }


    /** @return size of the array */
    public int size() {
        return content.length;
    }

    public void arraycopy(int srcIdx, Object dest, int destIndex, int length) {
        System.arraycopy(content, srcIdx, dest, destIndex, length);
    }

    public final boolean isEmpty() {
        return content.length == 0;
    }

    public boolean contains(S op) {
        for (S el : content) {
            if (Objects.equals(el, op)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Convert the array to a Java array (O(n))
     *
     * @throws ClassCastException if T is not a supertype of S
     */
    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] array) {
        T[] result;
        if (array.length < size()) {
            Class<? extends Object[]> arrayClass = array.getClass();
            assert arrayClass.isArray() : "@AssumeAssertion(nullness): arrayClass is an array";
            result = (T[]) Array.newInstance(arrayClass.getComponentType(), content.length);
        } else {
            result = array;
        }
        System.arraycopy(content, 0, result, 0, content.length);
        return result;
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(content);
    }

    @Override
    public boolean equals(@Nullable Object o) {
        if (o == this) {
            return true;
        }

        final @Nullable Object @Nullable [] cmp;
        if (o instanceof ImmutableArray) {
            cmp = ((ImmutableArray<?>) o).content;
        } else {
            return false;
        }

        if (cmp.length != content.length) {
            return false;
        }

        for (int i = 0; i < content.length; i++) {
            if (!Objects.equals(content[i], cmp[i])) {
                return false;
            }
        }
        return true;
    }

    @Override
    public String toString() {
        return Strings.formatAsList(this, "[", ",", "]");
    }

    @Override
    public Iterator<S> iterator() {
        return new ArrayIterator<S>(this);
    }

    private static class ArrayIterator<T extends @Nullable Object> implements Iterator<T> {

        private int i = 0;
        private final ImmutableArray<T> coll;

        ArrayIterator(ImmutableArray<T> coll) {
            this.coll = coll;
        }

        @Override
        public boolean hasNext() {
            return i < coll.size();
        }

        @Override
        public T next() {
            return coll.get(i++);
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException(
                "Illegal modification access on unmodifiable array.");
        }
    }

    /**
     * Convert an {@link ImmutableArray} to an {@link ImmutableList}.
     *
     * @return This element converted to an {@link ImmutableList}.
     */
    public ImmutableList<S> toImmutableList() {
        ImmutableList<S> ret = ImmutableSLList.nil();
        for (S s : this) {
            ret = ret.prepend(s);
        }
        return ret.reverse();
    }

    /**
     * Convert an {@link ImmutableArray} to a {@link List}.
     *
     * @return A freshly created {@link List} containing the elements of this array.
     */
    public List<S> toList() {
        List<S> result = new ArrayList<>();
        for (S s : this) {
            result.add(s);
        }
        return result;
    }


    /**
     * A stream object for this collection.
     *
     * @return a non-null stream object
     */
    public Stream<S> stream() {
        return StreamSupport.stream(spliterator(), false);
    }
}
