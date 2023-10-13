/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

/**
 * Wrapper around an object that implements {@link EqualsModProofIrrelevancy}.
 * Forwards calls to {@link #equals(Object)} and {@link #hashCode()} to
 * {@link EqualsModProofIrrelevancy#equalsModProofIrrelevancy(Object)} and
 * {@link EqualsModProofIrrelevancy#hashCodeModProofIrrelevancy()}.
 *
 * @param <T> type to wrap
 * @author Arne Keller
 */
public class EqualsModProofIrrelevancyWrapper<T extends EqualsModProofIrrelevancy> {
    /**
     * The wrapped object.
     */
    private final T inner;

    /**
     * Construct a new wrapper for the provided object. The provided object must implement
     * {@link EqualsModProofIrrelevancy}.
     *
     * @param inner object to wrap
     */
    public EqualsModProofIrrelevancyWrapper(T inner) {
        this.inner = inner;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        EqualsModProofIrrelevancyWrapper<?> that = (EqualsModProofIrrelevancyWrapper<?>) o;

        return inner != null ? inner.equalsModProofIrrelevancy(that.inner) : that.inner == null;
    }

    @Override
    public int hashCode() {
        return inner != null ? inner.hashCodeModProofIrrelevancy() : 0;
    }
}
