package de.uka.ilkd.key.util;

import org.key_project.util.EqualsModProofIrrelevancy;

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
