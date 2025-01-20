/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.util;

import java.util.Collection;
import java.util.Map;

/**
 * <p>
 * Instances of this class are used to reset overwritten {@link Object#equals(Object)} and
 * {@link Object#hashCode()} methods of the wrapped child element to the default Java implementation
 * with referenced based equality.
 * </p>
 * <p>
 * A possible use case of this class is for instance the usage in {@link Collection} like
 * {@link Map}s. Imagine the following scenario: A {@code Map<Customer, ...>} maps {@code Customer}
 * instances to something. Each customer has a unique ID and {@link Object#equals(Object)} and
 * {@link Object#hashCode()} is overwritten to compare instances by their unique ID. If now a clone
 * of a {@code Customer} instance exists the {@link Map} will return the value object for the
 * original {@code Customer} instance. The {@link Map} can not separate between original and clone.
 * If instead a {@code Map<EqualsHashCodeResetter<Customer>, ...>} is used original and clone are
 * different because the default Java implementation with referenced based equality is used.
 * </p>
 *
 * @param wrappedElement The wrapped elements on that {@link #equals(Object)} and {@link #hashCode()} is reset to
 *                       default Java implementation.
 * @author Martin Hentschel
 */
public record EqualsHashCodeResetter<T>(T wrappedElement) {
    /**
     * Constructor
     *
     * @param wrappedElement the wrapped elements on that {@link #equals(Object)} and
     *                       {@link #hashCode()} is reset to default Java implementation.
     */
    public EqualsHashCodeResetter {
    }

    /**
     * Overwritten to restore default Java implementation with reference based equality.
     */
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof EqualsHashCodeResetter<?>) {
            return wrappedElement() == ((EqualsHashCodeResetter<?>) obj).wrappedElement();
        } else {
            return false;
        }
    }

    /**
     * Overwritten to restore default Java implementation with reference based equality.
     */
    @Override
    public int hashCode() {
        return System.identityHashCode(wrappedElement());
    }

    /**
     * Returns the wrapped elements on that {@link #equals(Object)} and {@link #hashCode()} is reset
     * to default Java implementation.
     *
     * @return The wrapped element.
     */
    @Override
    public T wrappedElement() {
        return wrappedElement;
    }
}
