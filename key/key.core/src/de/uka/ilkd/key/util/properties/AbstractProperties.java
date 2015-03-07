package de.uka.ilkd.key.util.properties;


import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;

public abstract class AbstractProperties implements Properties {

    private final Map<Property<?>, Set<PropertyListener>> listenerMap =
            new IdentityHashMap<Property<?>, Set<PropertyListener>>();

    private final Set<PropertyListener> globalListeners =
            new HashSet<Properties.PropertyListener>();

    @Override
    public void addPropertyListener(Property<?> property, PropertyListener listener) {
        if(property == null) {
            globalListeners.add(listener);
        } else {
            Set<PropertyListener> list = listenerMap.get(property);
            if(list == null) {
                list = new HashSet<PropertyListener>();
                listenerMap.put(property, list);
            }
            list.add(listener);
        }
    }

    @Override
    public void removePropertyListener(Property<?> property, PropertyListener listener) {
        if(property == null) {
            globalListeners.remove(listener);
        } else {
            Set<PropertyListener> list = listenerMap.get(property);
            if(list != null) {
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
        if(oldValue == null || !oldValue.equals(newValue)) {
            Set<PropertyListener> list = listenerMap.get(property);
            if(list != null) {
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
