/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.function.BiPredicate;
import java.util.function.ToIntFunction;

/**
 * Wrapper around an object that implements alternative equality and hash code methods.
 * Forwards calls to {@link #equals(Object)} and {@link #hashCode()} to
 * {@link #equalityCmp} and
 * {@link #hasher}.
 *
 * @param <T> type to wrap
 * @author Arne Keller
 */
@SuppressWarnings("nullness")
public class EqualsAndHashCodeDelegator<T> {
    /**
     * The wrapped object.
     */
    private final T inner;
    private final BiPredicate<T, T> equalityCmp;
    private final ToIntFunction<T> hasher;

    /**
     * Construct a new wrapper for the provided object.
     *
     * @param inner object to wrap
     * @param equalityCmp the equality method to be used
     * @param hasher the hash method to be used
     */
    public EqualsAndHashCodeDelegator(T inner,
            BiPredicate<T, T> equalityCmp,
            ToIntFunction<T> hasher) {
        this.inner = inner;
        this.equalityCmp = equalityCmp;
        this.hasher = hasher;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        EqualsAndHashCodeDelegator<?> that = (EqualsAndHashCodeDelegator<?>) o;

        return inner != null ? equalityCmp.test(inner, (T) that.inner) : that.inner == null;
    }

    @Override
    public int hashCode() {
        return inner != null ? hasher.applyAsInt(inner) : 0;
    }
}
