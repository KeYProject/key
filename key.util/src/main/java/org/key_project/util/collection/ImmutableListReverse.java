/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Objects;
import java.util.function.Predicate;

import org.jspecify.annotations.Nullable;

/// Represents a reversed view of an immutable list.
///
/// This class provides a lazy reversed view of another [ImmutableList]. Instead of
/// physically reversing the elements, it wraps an existing list and delegates operations
/// with appropriate index/value transformations to present a reversed order.
///
/// **You should never ever need to use this class directly.** Use the interface.
///
/// @param <T> the type of elements in this list (may be nullable)
/// @author Alexander Weigl
/// @version 1 (25.04.26)
final class ImmutableListReverse<T extends @Nullable Object> implements ImmutableList<T> {
    private final ImmutableList<T> inner;

    ImmutableListReverse(ImmutableList<T> inner) {
        this.inner = inner;
    }

    @Override
    public T head() {
        return inner.last();
    }

    @Override
    public boolean exists(Predicate<? super T> predicate) {
        return inner.exists(predicate);
    }

    /// Extra fast: reverse(reverse(list)) is idempotent!
    @Override
    public ImmutableList<T> reverse() {
        return inner;
    }

    @Override
    public int size() {
        return inner.size();
    }

    @Override
    public boolean isEmpty() {
        return inner.isEmpty();
    }

    @Override
    public ImmutableList<T> removeFirst(T obj) {
        // TODO this is hard to implement
        return new ImmutableListReverse<>(inner.removeFirst(obj));
    }

    @Override
    public ImmutableList<T> removeAll(T obj) {
        return new ImmutableListReverse<>(inner.removeAll(obj));
    }

    @Override
    public T get(int idx) {
        if (idx < 0 || idx >= size()) {
            throw new IndexOutOfBoundsException("Index: " + idx + ", Size: " + size());
        }
        return inner.get(size() - 1 - idx);
    }

    @Override
    public boolean equals(@Nullable Object obj) {
        if (obj == this)
            return true;
        if (obj instanceof ImmutableListReverse<?> other)
            return Objects.equals(this.inner, other.inner);

        if (obj instanceof ImmutableList<?> other)
            return ImmutableList.equals(this, other);

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
