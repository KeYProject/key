/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;


import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A base class for own settings based on properties.
 *
 * @author weigl
 */
@NullMarked
public abstract class AbstractPropertiesSettings extends AbstractSettings {

    private static final String SET_DELIMITER = ",";
    private static final Function<String, Integer> parseInt = Integer::parseInt;
    private static final Function<String, Float> parseFloat = Float::parseFloat;
    private static final Function<String, Boolean> parseBoolean = Boolean::parseBoolean;
    private static final Function<String, Double> parseDouble = Double::parseDouble;

    /**
     * category of this settings w/o brackets, e.g, "View" for "[View]".
     * This will prefix to every property entry.
     */
    protected final String category;


    /**
     * Collection of listeners to notify when a setting changes its value.
     */
    protected final List<PropertyEntry<?>> propertyEntries = new LinkedList<>();

    protected AbstractPropertiesSettings(String category) {
        this.category = category;
    }

    private static Set<String> parseStringSet(String o) {
        Set<String> set = new TreeSet<>();
        for (String entry : o.split(SET_DELIMITER)) {
            if (!entry.isEmpty()) {
                set.add(entry.trim());
            }
        }
        return set;
    }

    private static String stringSetToString(Set<String> set) {
        return String.join(SET_DELIMITER, set);
    }

    /**
     * Translation of a string to a list of strings by using {@link #SET_DELIMITER}.
     *
     * @param str a nonnull, emptible string
     * @return a possible empty, list of strings
     * @see #stringListToString(List)
     */
    private static @NonNull List<String> parseStringList(@NonNull String str) {
        // escape special chars (in particular the comma)
        return Arrays.stream(str.split(SET_DELIMITER)).map(SettingsConverter::decodeString)
                .collect(Collectors.toCollection(ArrayList::new));
    }

    /**
     * @param seq a string list
     * @return the strings concatenated with {@link #SET_DELIMITER}
     */
    private static @NonNull String stringListToString(@NonNull List<String> seq) {
        // escape special chars (in particular the comma)
        return seq.stream().map(SettingsConverter::encodeString)
                .collect(Collectors.joining(SET_DELIMITER));
    }

    @Override
    public void readSettings(Configuration props) {
        var cat = props.getSection(category);
        if (cat == null)
            return;

        for (PropertyEntry<?> it : propertyEntries) {
            it.setValue(cat.get(it.getKey()));
        }
    }

    @Override
    public void writeSettings(Configuration props) {
        var cat = props.getOrCreateSection(category);
        for (PropertyEntry<?> it : propertyEntries) {
            cat.set(it.getKey(), it.get());
        }
    }

    protected PropertyEntry<Double> createDoubleProperty(String key, double defValue) {
        PropertyEntry<Double> pe = new DirectPropertyEntry<>(key, defValue);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Integer> createIntegerProperty(String key, int defValue) {
        PropertyEntry<Integer> pe = new DirectPropertyEntry<>(key, defValue) {
            @Override
            public void setValue(@Nullable Object value) {
                if (value instanceof Integer i) {
                    set(i);
                }
                if (value instanceof Long i) {
                    set(i.intValue());
                }
            }
        };
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Float> createFloatProperty(String key, float defValue) {
        PropertyEntry<Float> pe = new DirectPropertyEntry<>(key, defValue);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<String> createStringProperty(String key, String defValue) {
        PropertyEntry<String> pe = new DirectPropertyEntry<>(key, defValue);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Boolean> createBooleanProperty(String key, boolean defValue) {
        PropertyEntry<Boolean> pe = new DirectPropertyEntry<>(key, defValue);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Set<String>> createStringSetProperty(String key, Set<String> defValue) {
        PropertyEntry<Set<String>> pe = new DirectPropertyEntry<>(key, defValue) {
            @Override
            public void setValue(@Nullable Object value) {
                if (value instanceof List<?> seq) {
                    set(new TreeSet<>((Collection<String>) seq));
                }
            }
        };
        propertyEntries.add(pe);
        return pe;
    }

    /**
     * Creates a string list property.
     *
     * @param key the key value of this property inside {@link Properties} instance
     * @param defValue a default value
     * @return returns a {@link PropertyEntry}
     */
    protected PropertyEntry<List<String>> createStringListProperty(@NonNull String key,
            @Nullable List<String> defValue) {
        PropertyEntry<List<String>> pe = new DirectPropertyEntry<>(key, defValue);
        propertyEntries.add(pe);
        return pe;
    }


    /// This interface describes properties or options in an [AbstractPropertiesSettings] class.
    /// A [PropertyEntry] is parameterize in a type its value holds, additionally it has name (to
    /// store and read it
    /// from configuration files), often a default.
    ///
    /// @param <T>
    public interface PropertyEntry<T extends @Nullable Object> {
        /**
         * The name (or key) to find this value inside a configuration file. It should also be the
         * key
         * in {@link java.beans.PropertyChangeEvent}s.
         */
        String getKey();

        /**
         * Sets this value of this property. Should trigger {@link java.beans.PropertyChangeEvent}
         * if necessary.
         *
         * @param value the new configuration value
         */
        void set(T value);

        /**
         * Returns the current configuration value.
         */
        T get();


        /// This method allows to set the property using an arbitray object which is allowed in
        /// the configuration hierarchy. This methods may throw an exception on unexpected value
        /// types.
        ///
        /// Especially, the following should not result into change of the value for a property:
        /// ```java
        /// setValue(value())
        /// ```
        ///
        /// @param value an object of the [Configuration] hierarchy
        void setValue(@Nullable Object value);

        /**
         * Returns the representation of this configuration value to store it inside a
         * {@link Configuration}
         * object.
         *
         * @return an object compatible with {@link #setValue(Object)}
         */
        Object value();

        /// returns true if the property is set.
        boolean isSet();
    }

    /// @param <T>
    public abstract class SimplePropertyEntry<T extends @Nullable Object>
            implements PropertyEntry<T> {
        private final String key;
        private final T defaultValue;
        private T currentValue;

        SimplePropertyEntry(String key, T defaultValue) {
            this.key = key;
            this.defaultValue = defaultValue;
        }

        @Override
        public String getKey() {
            return key;
        }

        @Override
        public void set(T value) {
            var old = currentValue;
            currentValue = value;
            firePropertyChange(getKey(), old, value);
        }

        @Override
        public T get() {
            return currentValue != null ? currentValue : defaultValue;
        }

        @Override
        public boolean isSet() {
            return currentValue != null;
        }
    }

    /**
     * A base class for any configuration properties which is directly supported by the
     * configuration.
     *
     * @param <T> type of the value, supported by {@link Configuration}
     * @see Configuration#allowedValueType(Object)
     */
    public class DirectPropertyEntry<T extends @Nullable Object> extends SimplePropertyEntry<T> {
        DirectPropertyEntry(String key, T defaultValue) {
            super(key, defaultValue);
        }

        @Override
        public void setValue(@Nullable Object value) {
            set((T) value);
        }

        @Override
        public Object value() {
            return get();
        }
    }

    /**
     * A base class for any configuration properties which are stored into a string representation.
     *
     * @param <T> the value of the property
     */
    public class DefaultPropertyEntry<T extends @Nullable Object> extends SimplePropertyEntry<T> {
        private final Function<String, T> convert;
        private final Function<T, String> toString;

        public DefaultPropertyEntry(String key, T defaultValue,
                Function<String, T> convert, Function<T, String> toString) {
            super(key, defaultValue);
            this.convert = convert;
            this.toString = toString;
        }

        @Override
        public void setValue(@Nullable Object value) {
            if (value == null) {
                set(null);
                return;
            }

            if (value instanceof String s) {
                set(convert.apply(s));
                return;
            }

            throw new IllegalArgumentException(
                "Type %s is not supported for option %s".formatted(value.getClass(), getKey()));
        }

        @Override
        public String value() {
            var v = get();
            if (v == null) {
                return null;
            } else {
                return toString.apply(v);
            }
        }
    }
}
