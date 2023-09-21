/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.properties;


import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;

public abstract class AbstractProperties implements Properties {

    private final Map<Property<?>, Set<PropertyListener>> listenerMap =
        new IdentityHashMap<>();

    private final Set<PropertyListener> globalListeners =
        new HashSet<>();

    @Override
    public void addPropertyListener(Property<?> property, PropertyListener listener) {
        if (property == null) {
            globalListeners.add(listener);
        } else {
            Set<PropertyListener> list =
                listenerMap.computeIfAbsent(property, k -> new HashSet<>());
            list.add(listener);
        }
    }

    @Override
    public void removePropertyListener(Property<?> property, PropertyListener listener) {
        if (property == null) {
            globalListeners.remove(listener);
        } else {
            Set<PropertyListener> list = listenerMap.get(property);
            if (list != null) {
                list.remove(listener);
            }
        }
    }

    @Override
    public void removePropertyListener(PropertyListener listener) {
        globalListeners.remove(listener);
        for (Set<PropertyListener> list : listenerMap.values()) {
            list.remove(listener);
        }
    }

    protected <T> void firePropertyChange(Property<T> property, T oldValue, T newValue) {
        if (oldValue == null || !oldValue.equals(newValue)) {
            Set<PropertyListener> list = listenerMap.get(property);
            if (list != null) {
                for (PropertyListener listener : list) {
                    listener.propertyChanged(property, oldValue, newValue);
                }
            }
            for (PropertyListener listener : globalListeners) {
                listener.propertyChanged(property, oldValue, newValue);
            }
        }
    }


    @Override
    public abstract Properties clone();
}
