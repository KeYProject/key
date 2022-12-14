package de.uka.ilkd.key.util;

import org.key_project.util.EqualsModProofIrrelevancy;

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
    public final T inner;

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
