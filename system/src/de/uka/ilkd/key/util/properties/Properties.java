package de.uka.ilkd.key.util.properties;


import java.util.concurrent.atomic.AtomicInteger;


public interface Properties {

    public final static class Property<T> {
        private static AtomicInteger counter = new AtomicInteger(-1);
        private final String name;
        private final Class<T> type;
        private final int number = counter.incrementAndGet();

        public Property(Class<T> type, String name) {
            this.type = type;
            this.name = name;
        }

        @Override
        public String toString() {
            return "Property[" + number + ": " + name + " (" + type + ")]";
        }

        public Class<T> getType() {
            return type;
        }

        public String getName() {
            return name;
        }

        public int getNumber() {
            return number;
        }
    }

    public static interface PropertyListener {
        public <T> void propertyChanged(Property<T> property, T oldValue, T newValue);
    }

    public <T> void put(Property<T> property, T value);

    public <T> T get(Property<T> property);

    public <T> void remove(Property<T> property);

    public void addPropertyListener(Property<?> property, PropertyListener listener);

    public void removePropertyListener(Property<?> property, PropertyListener listener);

    public void removePropertyListener(PropertyListener listener);

    public Properties clone();

    public int size();

}