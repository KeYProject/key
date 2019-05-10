package de.uka.ilkd.key.settings;


import java.util.EventObject;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;
import java.util.function.Function;

/**
 * A base class for own settings based on properties.
 *
 * @author weigl
 */
public abstract class AbstractPropertiesSettings implements Settings {
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

    public boolean isInitialized() {
        return properties != null;
    }

    @Override
    public void readSettings(Properties props) {
        assert props != null;
        propertyEntries.forEach(it -> {
            if (props.contains(it.getKey()))
                properties.setProperty(it.getKey(), props.getProperty(it.getKey()));
        });
    }

    @Override
    public void writeSettings(Properties props) {
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

    protected PropertyEntry<Boolean> createBooleanProperty(String key, boolean b) {
        PropertyEntry<Boolean> pe = new DefaultPropertyEntry<>(key, b, parseBoolean);
        propertyEntries.add(pe);
        return pe;
    }

    public interface PropertyEntry<T> {
        String getKey();

        void set(T value);

        T get();
    }


    class DefaultPropertyEntry<T> implements PropertyEntry<T> {
        private final String key;
        private final T defaultValue;
        private final Function<String, T> convert;

        private DefaultPropertyEntry(String key, T defaultValue, Function<String, T> convert) {
            this.key = key;
            this.defaultValue = defaultValue;
            this.convert = convert;
        }

        @Override
        public String getKey() {
            return key;
        }

        public void set(T value) {
            T old = get();
            if (!value.equals(old)) {
                properties.setProperty(key, value.toString());
                fireSettingsChange();
            }
        }

        public T get() {
            String v = properties.getProperty(key);
            if (v == null) {
                return defaultValue;
            } else {
                return convert.apply(v);
            }
        }
    }
}
