/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Objects;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import org.jspecify.annotations.Nullable;

/// Represents a concatenated immutable list composed of two sub-lists.
///
/// This class implements the [ImmutableList] interface using a lazy concatenation
/// approach. Instead of physically merging two lists, it maintains references to both
/// the left and right sub-lists and performs operations by delegating to them appropriately.
///
/// **You should never ever need to use this class directly.** Use the interface.
///
/// @param <T> the type of elements in this list (may be nullable)
/// @author Alexander Weigl
/// @version 1 (25.04.26)
final class ImmutableListConcat<T extends @Nullable Object>
        implements ImmutableList<T> {
    private final ImmutableList<T> left;
    private final ImmutableList<T> right;

    ImmutableListConcat(ImmutableList<T> left, ImmutableList<T> right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public boolean exists(Predicate<? super T> predicate) {
        return left.exists(predicate) || right.exists(predicate);
    }

    @Override
    public int size() {
        return left.size() + right.size();
    }

    @Override
    public boolean isEmpty() {
        return left.isEmpty() && right.isEmpty();
    }

    @Override
    public ImmutableList<T> removeFirst(T obj) {
        // This is the tricky part. Removing first of an object, removes it either from the
        // first list if present or from the second if not present in the first list.

        if (left.isEmpty() && right.isEmpty()) {
            return ImmutableList.nil();
        }

        if (left.isEmpty()) {
            return right.removeFirst(obj);
        }

        if (right.isEmpty()) {
            return left.removeFirst(obj);
        }

        if (left.exists((it) -> Objects.equals(obj, it))) {
            return new ImmutableListConcat<>(left.removeFirst(obj), right);
        } else {
            return new ImmutableListConcat<>(left, right.removeFirst(obj));
        }
    }

    @Override
    public ImmutableList<T> removeAll(T obj) {
        return new ImmutableListConcat<>(left.removeAll(obj), right.removeAll(obj));
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
        return stream().map(Objects::toString).collect(Collectors.joining(", "));
    }

    @Override
    public T get(int idx) {
        if (idx < 0 || idx >= size()) {
            throw new IndexOutOfBoundsException("Index: " + idx + ", Size: " + size());
        }

        if (idx < left.size()) {
            return left.get(idx);
        }

        return right.get(idx - left.size());
    }
}
