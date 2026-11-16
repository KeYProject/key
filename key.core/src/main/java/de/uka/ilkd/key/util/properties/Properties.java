/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.util.properties;


import java.util.concurrent.atomic.AtomicInteger;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;



/// WEIGL: These classes are redundant with {@link PropertyEntry}
/// {@link PropertyEntry} is also prepared for {@link Configuration} which provides
/// a type safe access.
@NullMarked
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
        <T> void propertyChanged(Property<T> property, @Nullable T oldValue, @Nullable T newValue);
    }

    <T> void put(Property<T> property, @Nullable T value);

    <T> @Nullable T get(Property<T> property);

    <T> void remove(Property<T> property);

    void addPropertyListener(@Nullable Property<?> property, PropertyListener listener);

    void removePropertyListener(@Nullable Property<?> property, PropertyListener listener);

    void removePropertyListener(PropertyListener listener);

    Properties clone();

    int size();

}
