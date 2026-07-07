/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Stream;

import org.jspecify.annotations.Nullable;

/// Represents an immutable list backed by a standard Java [List].
///
/// This class provides an immutable wrapper around a collection, implementing the
/// [ImmutableList] interface. The underlying data is stored in an unmodifiable
/// [ArrayList], ensuring that all operations preserve immutability.
///
/// **You should never ever need to use this class directly.** Use the interface.
///
/// @param <T> the type of elements in this list (may be nullable)
/// @author Alexander Weigl
/// @version 1 (25.04.26)
@SuppressWarnings("unchecked")
final class ImmutableListList<T extends @Nullable Object> implements ImmutableList<T> {
    private final List<T> data;

    private ImmutableListList(List<T> data) {
        this.data = data;
    }

    public ImmutableListList(Collection<T> data) {
        this(Collections.unmodifiableList(new ArrayList<>(data)));
    }

    /// **Danger:** This factory does not guarantee immutability if data has leaked!
    /// Use with care!
    static <T> ImmutableListList<T> createDirectlyWithoutImmutableGuarantee(List<T> data) {
        return new ImmutableListList<>(data);
    }

    @Override
    public T head() {
        return data.getFirst();
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
        return data.iterator();
    }

    @Override
    public int size() {
        return data.size();
    }

    @Override
    public boolean isEmpty() {
        return data.isEmpty();
    }

    @Override
    public ImmutableList<T> removeFirst(T obj) {
        int pos = -1;
        for (int i = 0; i < data.size(); i++) {
            var datum = data.get(i);
            if (Objects.equals(obj, datum)) {
                pos = i;
                break;
            }
        }

        if (pos != -1) {
            var newData = new ArrayList<>(data);
            newData.remove(pos);
            return new ImmutableListList<>(newData);
        }

        return this;
    }

    @Override
    public ImmutableList<T> removeAll(T obj) {
        return stream().filter(it -> !Objects.equals(it, obj)).collect(ImmutableList.collector());
    }

    @Override
    public Stream<T> stream() {
        return data.stream();
    }

    @Override
    public ImmutableList<T> filter(Predicate<? super T> predicate) {
        return ImmutableList.super.filter(predicate);
    }

    @Override
    public T last() {
        return data.getLast();
    }

    @Override
    public T get(int idx) {
        if (idx < 0 || idx >= data.size()) {
            throw new IndexOutOfBoundsException("Given index out of bounds.");
        }
        return data.get(idx);
    }


    @Override
    public boolean equals(@Nullable Object o) {
        if (o == null)
            return false;
        if (o instanceof ImmutableListList<?> that) {
            return Objects.equals(data, that.data);
        }
        if (o instanceof ImmutableList<?> that) {
            return ImmutableList.equals(this, that);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return ImmutableList.hash(this);
    }

    @Override
    public String toString() {
        return ImmutableList.toString(this);
    }
}
