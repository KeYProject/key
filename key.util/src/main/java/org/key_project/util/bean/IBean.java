/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.bean;

import java.beans.PropertyChangeListener;

/**
 * <p>
 * Defines the methods that a Java bean must have.
 * </p>
 * <p>
 * Implementation of this interface should subclass from {@link Bean} if possible.
 * </p>
 *
 * @author Martin Hentschel
 * @see Bean
 */
public interface IBean {
    /**
     * Adds the given listener.
     *
     * @param listener The listener to add.
     */
    void addPropertyChangeListener(PropertyChangeListener listener);

    /**
     * Adds the given listener for the given property only.
     *
     * @param propertyName The property to observe.
     * @param listener The listener to add.
     */
    void addPropertyChangeListener(String propertyName, PropertyChangeListener listener);

    /**
     * Removes the given listener.
     *
     * @param listener The listener to remove.
     */
    void removePropertyChangeListener(PropertyChangeListener listener);

    /**
     * Removes the given listener from the given property.
     *
     * @param propertyName The property to no longer observe.
     * @param listener The listener to remove.
     */
    void removePropertyChangeListener(String propertyName, PropertyChangeListener listener);

    /**
     * Returns all listeners.
     *
     * @return The listeners.
     */
    PropertyChangeListener[] getPropertyChangeListeners();

    /**
     * Returns all listeners of the given property.
     *
     * @param propertyName The property.
     * @return The listeners of the given property.
     */
    PropertyChangeListener[] getPropertyChangeListeners(String propertyName);

    /**
     * Checks if listeners are available.
     *
     * @return {@code true} listeners available, {@code false} no listeners are available.
     */
    boolean hasListeners();

    /**
     * Checks if listeners are available for the given property.
     *
     * @param propertyName The property name.
     * @return {@code true} listeners available for the property, {@code false} no listeners are
     *         available for the property.
     */
    boolean hasListeners(String propertyName);

    /**
     * Checks if the given listener is already available.
     *
     * @param listener The listener to check.
     * @return {@code true} listener is available, {@code false} listener is not available.
     */
    boolean hasListener(PropertyChangeListener listener);

    /**
     * Checks if the given listener is available for the given property.
     *
     * @param propertyName The property.
     * @param listener The listener to check.
     * @return {@code true} listener is available for the property, {@code false} listener is not
     *         available for the property.
     */
    boolean hasListener(String propertyName, PropertyChangeListener listener);
}
