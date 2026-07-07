/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Objects;

import org.jspecify.annotations.Nullable;

/// Represents a view of a portion / span of an immutable list.
///
/// This class provides a lazy sub-list view of another [ImmutableList]. Instead of
/// copying elements, it wraps an existing list with start and end indices to present a
/// restricted view of the underlying data.
///
/// **You should never ever need to use this class directly.** Use the interface.
///
/// @param <T> the type of elements in this list (may be nullable)
/// @author Alexander Weigl
/// @version 1 (25.04.26)
final class ImmutableListSubList<T extends @Nullable Object>
        implements ImmutableList<T> {

    private final ImmutableList<T> list;
    private final int start;
    private final int end;

    public ImmutableListSubList(ImmutableList<T> ts, int startInclusive) {
        this(ts, startInclusive, ts.size());
    }

    ImmutableListSubList(ImmutableList<T> list, int start, int end) {
        if (end > list.size()) {
            throw new IllegalArgumentException("The 'end' is larger than the size of the list");
        }

        if (start < 0) {
            throw new IllegalArgumentException(
                "The 'start' needs to be positive. Negative indices are not allowed.");
        }

        if (start > end) {
            throw new IllegalArgumentException(
                "The 'start' is larger than the given 'end' of the list");
        }
        this.list = list;
        this.start = start;
        this.end = end;
    }

    @Override
    public Iterator<T> iterator() {
        return new Iterator<>() {
            int pos = start;

            @Override
            public boolean hasNext() {
                return pos < end;
            }

            @Override
            public T next() {
                return list.get(pos++);
            }
        };
    }

    @Override
    public int size() {
        return end - start;
    }

    @Override
    public boolean isEmpty() {
        return size() == 0;
    }

    @Override
    public ImmutableList<T> removeFirst(T obj) {
        var list = new ArrayList<T>();
        for (var t : this) {
            if (!Objects.equals(t, obj)) {
                list.add(t);
            }
        }
        return ImmutableList.fromList(list);
    }

    @Override
    public ImmutableList<T> removeAll(T obj) {
        return stream().filter(it -> !Objects.equals(obj, it)).collect(ImmutableList.collector());
    }

    @Override
    public T get(int idx) {
        var realIdx = start + idx;
        if (0 <= realIdx && realIdx < end) {
            return list.get(realIdx);
        }
        throw new IndexOutOfBoundsException();
    }

    @Override
    public boolean equals(@Nullable Object obj) {
        if (obj == this)
            return true;
        if (obj instanceof ImmutableList<?> other) {
            return ImmutableList.equals(this, other);
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
