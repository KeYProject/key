package de.uka.ilkd.key.util.properties;

import java.util.IdentityHashMap;

public class MapProperties extends AbstractProperties {

    private final IdentityHashMap<Object, Object> map;

    public MapProperties() {
        map = new IdentityHashMap<Object, Object >();
    }

    public MapProperties(int expectedSize) {
        map = new IdentityHashMap<Object, Object>(expectedSize);
    }

    public MapProperties(MapProperties original) {
        map = (IdentityHashMap) original.map.clone();
    }
    
    /* (non-Javadoc)
     * @see jatc.util.Properties#put(jatc.util.MapProperties.Property, T)
     */
    @Override
    public <T> void put(Property<T> property, T value) {
        T oldValue = get(property);
        // double check typing
        property.getType().cast(value);
        map.put(property, value);
        firePropertyChange(property, oldValue, value);
    }

    /* (non-Javadoc)
     * @see jatc.util.Properties#get(jatc.util.MapProperties.Property)
     */
    @Override
    public <T> T get(Property<T> property) {
        return property.getType().cast(map.get(property));
    }

    @Override
    public String toString() {
        return map.toString();
    }

    /* (non-Javadoc)
     * @see jatc.util.Properties#remove(jatc.util.MapProperties.Property)
     */
    @Override
    public <T> void remove(Property<T> property) {
        map.remove(property);
    }


    @Override
    public Properties clone() {
        return new MapProperties(this);
    }


    @Override
    public int size() {
        return map.size();
    }
}