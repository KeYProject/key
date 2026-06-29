/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.lang.reflect.Array;
import java.util.Arrays;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Stream;

import org.jspecify.annotations.Nullable;

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.04.26)
 */
final class ImmutableListArray<T extends @Nullable Object> implements ImmutableList<T> {
    private final T[] data;

    public ImmutableListArray(T[] data) {
        this.data = data;
    }

    @Override
    public T head() {
        try {
            return data[0];
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new NoSuchElementException("head() called on empty list");
        }
    }

    @Override
    public boolean exists(Predicate<? super T> predicate) {
        for (var datum : data) {
            if (predicate.test(datum)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public Iterator<T> iterator() {
        return new Iterator<>() {
            int pos = 0;

            @Override
            public boolean hasNext() {
                return pos < data.length;
            }

            @Override
            public T next() {
                return data[pos++];
            }
        };
    }

    @Override
    public int size() {
        return data.length;
    }

    @Override
    public boolean isEmpty() {
        return data.length == 0;
    }

    @SuppressWarnings("unchecked")
    @Override
    public ImmutableList<T> removeFirst(T obj) {
        int pos = -1;
        for (int i = 0; i < data.length; i++) {
            var datum = data[i];
            if (Objects.equals(obj, datum)) {
                pos = i;
                break;
            }
        }

        if (pos != -1) {
            if (size() == 1) {
                // spare all the stupid copying
                return ImmutableList.nil();
            }

            T[] newData = (T[]) new Object[data.length - 1];
            System.arraycopy(data, 0, newData, 0, pos);
            System.arraycopy(data, pos + 1, newData, pos, data.length - pos - 1);
            return new ImmutableListArray<>(newData);
        }

        return this;
    }

    @Override
    public ImmutableList<T> removeAll(T obj) {
        return stream().filter(it -> !Objects.equals(it, obj)).collect(ImmutableList.collector());
    }

    @SuppressWarnings({ "unchecked", "argument.type.incompatible" })
    @Override
    public <S extends @Nullable Object> S[] toArray(S[] array) {
        if (array.length == size()) {
            System.arraycopy(data, 0, array, 0, data.length);
            return array;
        } else {
            return (S[]) toArray(array.getClass().getComponentType());
        }
    }

    @SuppressWarnings("unchecked")
    @Override
    public <S extends @Nullable Object> S[] toArray(Class<S> type) {
        return toArray((S[]) Array.newInstance(type, size()));
    }

    @Override
    public Stream<T> stream() {
        return Arrays.stream(data);
    }

    @Override
    public ImmutableList<T> filter(Predicate<? super T> predicate) {
        return stream().filter(predicate).collect(ImmutableList.collector());
    }

    @SuppressWarnings("unchecked")
    @Override
    public <R extends @Nullable Object> ImmutableList<R> map(Function<? super T, R> function) {
        var newData = (R[]) new Object[size()];
        for (var i = 0; i < data.length; i++) {
            newData[i] = function.apply(data[i]);
        }
        return new ImmutableListArray<>(newData);
    }

    @Override
    public T last() {
        try {
            return data[data.length - 1];
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new NoSuchElementException("last() called on empty list");
        }
    }

    @Override
    public T get(int idx) {
        if (idx < 0 || idx >= size()) {
            throw new IndexOutOfBoundsException();
        }
        return data[idx];
    }

    @Override
    public boolean equals(@Nullable Object o) {
        if (o instanceof ImmutableListArray<?> that) {
            return Arrays.equals(data, that.data);
        }
        if (o instanceof ImmutableList<?> that) {
            return ImmutableList.equals(this, that);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(data);
    }
}
