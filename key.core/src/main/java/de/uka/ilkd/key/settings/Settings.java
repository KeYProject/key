/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.Properties;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;

/**
 * This interface is implemented by classes that are used to store settings for different proposes
 * (like active heuristics, which LDTs to use etc.)
 */
@NullMarked
public interface Settings {

    /**
     * This method transfers the given configuration information into the local states. The setter
     * methods are used
     * so {@link java.beans.PropertyChangeEvent} should be triggered accordingly to the new state.
     * <p>
     *
     * @param props a non-null references to a configuration object. The state of this object
     *              shall not be changed by the implementations.
     */
    void readSettings(Configuration props);

    /**
     * The internal state is stored in the given configuration object. The stored information must
     * be sufficient
     * to restore the local state.
     * <p>
     * The internal state shall not be changed by the implementations.
     *
     * @param props a non-null reference to a configration object, which state is modified
     *              accordingly to the local
     *              internal state.
     */
    void writeSettings(Configuration props);


    /**
     * Register a new listener which is triggered for changes on properties.
     *
     * @param listener a non-null reference
     * @see PropertyChangeSupport#addPropertyChangeListener(PropertyChangeListener)
     */
    void addPropertyChangeListener(PropertyChangeListener listener);

    /**
     * Removes the given listener.
     *
     * @param listener a non-null reference
     * @see PropertyChangeSupport#removePropertyChangeListener(PropertyChangeListener)
     */
    void removePropertyChangeListener(PropertyChangeListener listener);

    /**
     * Register a new listener which is triggered for changes on the specified property.
     *
     * @param propertyName the name for identification of the property
     * @param listener     the listener to be added
     * @see PropertyChangeSupport#addPropertyChangeListener(String, PropertyChangeListener)
     */
    void addPropertyChangeListener(String propertyName,
                                   PropertyChangeListener listener);

    /**
     * Removes the given listener from being triggered by changes of the specified property.
     *
     * @param propertyName the name for identification of the property
     * @param listener     the listener to be removed
     * @see PropertyChangeSupport#removePropertyChangeListener(String, PropertyChangeListener)
     */
    void removePropertyChangeListener(String propertyName, PropertyChangeListener listener);
}
