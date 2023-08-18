/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.properties;


import java.util.concurrent.atomic.AtomicInteger;


public interface Properties {

    final class Property<T> {
        private static final AtomicInteger counter = new AtomicInteger(-1);
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

    interface PropertyListener {
        <T> void propertyChanged(Property<T> property, T oldValue, T newValue);
    }

    <T> void put(Property<T> property, T value);

    <T> T get(Property<T> property);

    <T> void remove(Property<T> property);

    void addPropertyListener(Property<?> property, PropertyListener listener);

    void removePropertyListener(Property<?> property, PropertyListener listener);

    void removePropertyListener(PropertyListener listener);

    Properties clone();

    int size();

}
