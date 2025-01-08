/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;


import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * A base class for own settings based on properties.
 *
 * @author weigl
 */
public abstract class AbstractPropertiesSettings extends AbstractSettings {

    private static final String SET_DELIMITER = ",";
    private static final Function<String, Integer> parseInt = Integer::parseInt;
    private static final Function<String, Float> parseFloat = Float::parseFloat;
    private static final Function<String, Boolean> parseBoolean = Boolean::parseBoolean;
    private static final Function<String, Double> parseDouble = Double::parseDouble;

    /**
     * Properties stored in this settings object.
     * Updated by each {@link PropertyEntry} when a new non-null value is set.
     */
    protected Map<String, Object> properties = new TreeMap<>();

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

    public boolean isInitialized() {
        return properties != null;
    }

    @Override
    public void readSettings(Properties props) {
        propertyEntries.forEach(it -> {
            String value = props.getProperty(it.getKey());
            if (value != null) {
                it.parseFrom(value);
            }
        });
    }

    @Override
    public void writeSettings(Properties props) {
        for (PropertyEntry<?> entry : propertyEntries) {
            props.setProperty("[" + category + "]" + entry.getKey(), entry.value());
        }
    }


    @Override
    public void readSettings(Configuration props) {
        var cat = props.getSection(category);
        if (cat == null)
            return;
        propertyEntries.forEach(it -> {
            final var value = it.fromObject(cat.get(it.getKey()));
            if (value != null) {
                properties.put(it.getKey(), value);
            }
        });
    }

    @Override
    public void writeSettings(Configuration props) {
        var cat = props.getOrCreateSection(category);
        propertyEntries.forEach(it -> {
            cat.set(it.getKey(), it.get());
        });
    }

    protected PropertyEntry<Double> createDoubleProperty(String key, double defValue) {
        PropertyEntry<Double> pe =
            new DefaultPropertyEntry<>(key, defValue, parseDouble, (it) -> (double) it);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Integer> createIntegerProperty(String key, int defValue) {
        PropertyEntry<Integer> pe = new DefaultPropertyEntry<>(key, defValue, parseInt,
            (it) -> Math.toIntExact((Long) it));
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Float> createFloatProperty(String key, float defValue) {
        PropertyEntry<Float> pe =
            new DefaultPropertyEntry<>(key, defValue, parseFloat, (it) -> (float) (double) it);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<String> createStringProperty(String key, String defValue) {
        PropertyEntry<String> pe =
            new DefaultPropertyEntry<>(key, defValue, id -> id, Object::toString);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Boolean> createBooleanProperty(String key, boolean defValue) {
        PropertyEntry<Boolean> pe =
            new DefaultPropertyEntry<>(key, defValue, parseBoolean, (it) -> (Boolean) it);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Set<String>> createStringSetProperty(String key, String defValue) {
        PropertyEntry<Set<String>> pe = new DefaultPropertyEntry<>(key, parseStringSet(defValue),
            AbstractPropertiesSettings::parseStringSet,
            AbstractPropertiesSettings::stringSetToString,
            (it) -> new LinkedHashSet<>((Collection<String>) it));
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
            @Nullable String defValue) {
        PropertyEntry<List<String>> pe = new DefaultPropertyEntry<>(key, parseStringList(defValue),
            AbstractPropertiesSettings::parseStringList,
            AbstractPropertiesSettings::stringListToString, it -> (List<String>) it);
        propertyEntries.add(pe);
        return pe;
    }


    public interface PropertyEntry<T> {
        String getKey();

        void parseFrom(String value);

        void set(T value);

        T get();

        default void update() {
            set(get());
        }

        String value();

        T fromObject(@Nullable Object o);
    }


    class DefaultPropertyEntry<T> implements PropertyEntry<T> {
        private final String key;
        private final T defaultValue;
        private final Function<String, T> convert;
        private final Function<T, String> toString;

        private final Function<Object, T> fromObject;

        private DefaultPropertyEntry(String key, T defaultValue, Function<String, T> convert,
                Function<Object, T> fromObject) {
            this(key, defaultValue, convert, Objects::toString, fromObject);
        }

        private DefaultPropertyEntry(String key, T defaultValue, Function<String, T> convert,
                Function<T, String> toString, Function<Object, T> fromObject) {
            this.key = key;
            this.defaultValue = defaultValue;
            this.convert = convert;
            this.toString = toString;
            this.fromObject = fromObject;
        }

        @Override
        public String getKey() {
            return key;
        }

        @Override
        public void parseFrom(String value) {
            set(convert.apply(value));
        }

        @Override
        public void set(T value) {
            T old = get();
            // only store non-null values
            if (value != null) {
                properties.put(key, value);
                firePropertyChange(key, old, value);
            }
        }

        @Override
        public T get() {
            var v = properties.getOrDefault(key, defaultValue);
            if (v == null) {
                return defaultValue;
            } else {
                return (T) v;
            }
        }

        @Override
        public String value() {
            var v = get();
            if (v == null) {
                return toString.apply(defaultValue);
            } else {
                return toString.apply(v);
            }
        }

        @Override
        public T fromObject(@Nullable Object o) {
            return fromObject.apply(o);
        }
    }
}
