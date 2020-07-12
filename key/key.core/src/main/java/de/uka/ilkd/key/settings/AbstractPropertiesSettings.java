package de.uka.ilkd.key.settings;


import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;

/**
 * A base class for own settings based on properties.
 *
 * @author weigl
 */
public abstract class AbstractPropertiesSettings implements Settings {
    private static final String SET_DELIMITER = ",";
    private static Function<String, Integer> parseInt = Integer::parseInt;
    private static Function<String, Float> parseFloat = Float::parseFloat;
    private static Function<String, Boolean> parseBoolean = Boolean::parseBoolean;
    private static Function<String, Double> parseDouble = Double::parseDouble;

    /**
     *
     */
    protected Properties properties = new Properties();

    /**
     *
     */
    protected List<PropertyEntry<?>> propertyEntries = new LinkedList<>();

    /**
     *
     */
    protected List<SettingsListener> listenerList = new LinkedList<>();

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
     * Translation of a string to a list of string by using {@link #SET_DELIMITER}
     *
     * @param str a nonnull, emptible string
     * @return a possible empty, list of strings
     * @see #stringListToString(List)
     */
    private static @NotNull List<String> parseStringList(@NotNull String str) {
        return new ArrayList<>(Arrays.asList(str.split(SET_DELIMITER)));
    }

    /**
     * @param seq a string list
     * @return the strings concatenated with {@link #SET_DELIMITER}
     */
    private static @NotNull String stringListToString(@NotNull List<String> seq) {
        return String.join(SET_DELIMITER, seq);
    }

    public boolean isInitialized() {
        return properties != null;
    }

    @Override
    public void readSettings(Properties props) {
        assert props != null;
        propertyEntries.forEach(it -> {
            String value = props.getProperty(it.getKey());
            if (value != null) {
                properties.setProperty(it.getKey(), value);
            }
        });
    }

    @Override
    public void writeSettings(Properties props) {
        propertyEntries.forEach(it -> {
            it.update();
        });
        props.putAll(properties);
    }

    @Override
    public void addSettingsListener(SettingsListener l) {
        listenerList.add(l);
    }

    protected void fireSettingsChange() {
        for (SettingsListener listener : listenerList) {
            listener.settingsChanged(new EventObject(this));
        }
    }

    protected PropertyEntry<Double> createDoubleProperty(String key, double defValue) {
        PropertyEntry<Double> pe = new DefaultPropertyEntry<>(key, defValue, parseDouble);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Integer> createIntegerProperty(String key, int defValue) {
        PropertyEntry<Integer> pe = new DefaultPropertyEntry<>(key, defValue, parseInt);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Float> createFloatProperty(String key, float defValue) {
        PropertyEntry<Float> pe = new DefaultPropertyEntry<>(key, defValue, parseFloat);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<String> createStringProperty(String key, String defValue) {
        PropertyEntry<String> pe = new DefaultPropertyEntry<>(key, defValue, id -> id);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Boolean> createBooleanProperty(String key, boolean defValue) {
        PropertyEntry<Boolean> pe = new DefaultPropertyEntry<>(key, defValue, parseBoolean);
        propertyEntries.add(pe);
        return pe;
    }

    protected PropertyEntry<Set<String>> createStringSetProperty(String key, String defValue) {
        PropertyEntry<Set<String>> pe = new DefaultPropertyEntry<>(key,
                parseStringSet(defValue),
                AbstractPropertiesSettings::parseStringSet,
                AbstractPropertiesSettings::stringSetToString);
        propertyEntries.add(pe);
        return pe;
    }

    /**
     * Creates a string list property.
     *
     * @param key      the key value of this property inside {@link Properties} instance
     * @param defValue a default value
     * @return returns a {@link PropertyEntry}
     */
    protected PropertyEntry<List<String>> createStringListProperty(@NotNull String key,
                                                                   @Nullable String defValue) {
        PropertyEntry<List<String>> pe = new DefaultPropertyEntry<>(key,
                parseStringList(defValue),
                AbstractPropertiesSettings::parseStringList,
                AbstractPropertiesSettings::stringListToString);
        propertyEntries.add(pe);
        return pe;
    }


    public interface PropertyEntry<T> {
        String getKey();

        void set(String value);

        void set(T value);

        T get();

        default void update() {
            set(get());
        }

        String value();
    }


    class DefaultPropertyEntry<T> implements PropertyEntry<T> {
        private final String key;
        private final T defaultValue;
        private final Function<String, T> convert;
        private final Function<T, String> toString;

        private DefaultPropertyEntry(String key, T defaultValue, Function<String, T> convert) {
            this(key, defaultValue, convert, Objects::toString);
        }

        private DefaultPropertyEntry(String key, T defaultValue,
                                     Function<String, T> convert,
                                     Function<T, String> toString) {
            this.key = key;
            this.defaultValue = defaultValue;
            this.convert = convert;
            this.toString = toString;
        }

        @Override
        public String getKey() {
            return key;
        }

        @Override
        public void set(String value) {
            set(convert.apply(value));
        }

        @Override
        public void set(T value) {
            T old = get();
            properties.setProperty(key, toString.apply(value));
            if (!value.equals(old)) {
                fireSettingsChange();
            }
        }

        @Override
        public T get() {
            String v = properties.getProperty(key);
            if (v == null) {
                return defaultValue;
            } else {
                return convert.apply(v);
            }
        }

        @Override
        public String value() {
            String v = properties.getProperty(key);
            if (v == null) {
                return toString.apply(defaultValue);
            } else {
                return v;
            }
        }
    }
}
