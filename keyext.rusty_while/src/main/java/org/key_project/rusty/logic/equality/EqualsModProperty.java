package org.key_project.rusty.logic.equality;

public interface EqualsModProperty<T> {
    <V> boolean equalsModProperty(Object o, Property<T> property, V... v);

    /**
     * Computes the hash code according to the given ignored {@code property}.
     *
     * @param property the ignored property according to which the hash code is computed
     * @return the hash code of this object
     */
    int hashCodeModProperty(Property<T> property);
}
