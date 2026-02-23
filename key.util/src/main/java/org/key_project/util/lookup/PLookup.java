/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.lookup;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Supplier;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/// This class handles the management of services and implementations.
///
/// This class is a flexible alternative for a mediator. You can register and deregister
/// implementation for services. And also you can lookup them up. Multiple implementations are
/// possible; also notification on service change.
///
/// [PLookup] can be arranged hierarchical, incl. support for notification.
///
/// @author Alexander Weigl
/// @version 1 (15.03.19)
@NullMarked
public class PLookup {
    private final Map<Property<?>, @Nullable Object> serviceMap = new HashMap<>();

    @SuppressWarnings({ "assignment.type.incompatible", "argument.type.incompatible" })
    private final PropertyChangeSupport changeSupport = new PropertyChangeSupport(this);

    /// Get the current value for the given \`key\`.
    ///
    /// @param key the property to be looked-uped
    /// @param defaultValue the defaultValue return
    @SuppressWarnings("unchecked")
    public <T extends @Nullable Object> T get(Property<T> key, @Nullable T defaultValue) {
        return (T) serviceMap.getOrDefault(key, defaultValue);
    }

    @SuppressWarnings({ "unchecked", "cast.unsafe" })
    public <T> @Nullable T get(Property<T> key) {
        return (T) serviceMap.get(key);
    }

    @SuppressWarnings("unchecked")
    public <T extends @Nullable Object> @Nullable T putIfAbsent(Property<T> key,
            Supplier<@NonNull T> value) {
        return (T) serviceMap.computeIfAbsent(key, (k) -> value.get());
    }


    /// Sets the given `key` to the `value`.
    ///
    /// @param key the property
    /// @param value the new value to assigned to key
    /// @return the previous value assigned to `value`; possible null.
    @SuppressWarnings("unchecked")
    public <T extends @Nullable Object> T set(Property<T> key, T value) {
        var old = serviceMap.put(key, value);
        changeSupport.firePropertyChange(key.name(), old, value);
        return (T) old;
    }

    public <T> @Nullable Object remove(Property<T> key) {
        var old = serviceMap.remove(key);
        changeSupport.firePropertyChange(key.name(), old, null);
        return old;
    }

    public void dispose() {
        serviceMap.clear();
    }

    public void addPropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.addPropertyChangeListener(listener);
    }

    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        changeSupport.addPropertyChangeListener(propertyName, listener);
    }

    public void removePropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.removePropertyChangeListener(listener);
    }

    public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        changeSupport.removePropertyChangeListener(propertyName, listener);
    }
}
