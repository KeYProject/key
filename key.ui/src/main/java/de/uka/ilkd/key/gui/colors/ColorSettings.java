/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.colors;

import java.awt.*;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.IOException;
import java.io.Writer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.List;
import java.util.stream.Stream;

import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Configurable colors for KeY.
 * <p>
 * If you need a new color use: {@link #define(String, String, Color)}.
 *
 * @author Alexander Weigl
 * @version 1 (10.05.19)
 */
public class ColorSettings {
    public static final Path SETTINGS_FILE_NEW =
        PathConfig.getKeyConfigDir().resolve("colors.json");
    private static final Logger LOGGER = LoggerFactory.getLogger(ColorSettings.class);

    private static ColorSettings INSTANCE;
    private final Map<String, Object> properties = new TreeMap<>();
    private final List<ColorProperty> propertyEntries = new ArrayList<>(64);

    public ColorSettings(Configuration load) {
        // props.forEach((k, v) -> this.properties.put(k.toString(), v));
        load.getEntries().forEach(entry -> properties.put(entry.getKey(), entry.getValue()));
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    public static ColorSettings getInstance() {
        if (INSTANCE == null) {
            if (Files.exists(SETTINGS_FILE_NEW)) {
                try {
                    LOGGER.info("Load color settings from file {}", SETTINGS_FILE_NEW);
                    INSTANCE = new ColorSettings(Configuration.load(SETTINGS_FILE_NEW));
                    return INSTANCE;
                } catch (IOException e) {
                    LOGGER.error("Could not read {}", SETTINGS_FILE_NEW, e);
                }
            }
            INSTANCE = new ColorSettings(new Configuration());
            return INSTANCE;
        }
        return INSTANCE;
    }

    public static ColorProperty define(String key, String desc, Color color) {
        return getInstance().createColorProperty(key, desc, color, color);
    }

    public static ColorProperty define(String key, String desc, Color light, Color dark) {
        return getInstance().createColorProperty(key, desc, light, dark);
    }

    public static String toHex(Color c) {
        int a = c.getAlpha();
        int r = c.getRed();
        int g = c.getGreen();
        int b = c.getBlue();
        return String.format("#%02X%02X%02X%02X", a, r, g, b);
    }

    public static Color fromHex(String s) {
        long i = Long.decode(s);
        return new Color((int) ((i >> 16) & 0xFF), (int) ((i >> 8) & 0xFF), (int) (i & 0xFF),
            (int) ((i >> 24) & 0xFF));
    }

    public static Color invert(Color c) {
        return new Color(255 - c.getRed(), 255 - c.getGreen(), 255 - c.getBlue());
    }

    /**
     * Writes the current settings to default location.
     *
     * @see #SETTINGS_FILE_NEW
     */
    public void save() {
        LOGGER.info("Save color settings to: {}", SETTINGS_FILE_NEW.toAbsolutePath());
        try (Writer writer = Files.newBufferedWriter(SETTINGS_FILE_NEW)) {
            var config = new Configuration(properties);
            config.save(writer, "KeY's Colors");
            writer.flush();
        } catch (IOException ex) {
            LOGGER.error("Failed to save color settings", ex);
        }
    }

    private ColorProperty createColorProperty(String key, String description,
            Color defaultLight, Color defaultDark) {
        Optional<ColorProperty> item =
            getProperties().filter(it -> it.getKey().equals(key)).findFirst();
        if (item.isPresent()) {
            return item.get();
        }

        ColorProperty pe = new ColorProperty(key, description, defaultLight, defaultDark);
        propertyEntries.add(pe);
        return pe;
    }

    public Stream<ColorProperty> getProperties() {
        return propertyEntries.stream();
    }

    private final PropertyChangeSupport propertyChangeSupport = new PropertyChangeSupport(this);

    protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        propertyChangeSupport.firePropertyChange(propertyName, oldValue, newValue);
    }

    protected void firePropertyChange(String propertyName, int oldValue, int newValue) {
        propertyChangeSupport.firePropertyChange(propertyName, oldValue, newValue);
    }

    protected void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
        propertyChangeSupport.firePropertyChange(propertyName, oldValue, newValue);
    }

    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        propertyChangeSupport.addPropertyChangeListener(propertyName, listener);
    }

    public void removePropertyChangeListener(PropertyChangeListener listener) {
        propertyChangeSupport.removePropertyChangeListener(listener);
    }

    public void addPropertyChangeListener(PropertyChangeListener listener) {
        propertyChangeSupport.addPropertyChangeListener(listener);
    }

    public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        propertyChangeSupport.removePropertyChangeListener(propertyName, listener);
    }

    /**
     * A property for handling colors.
     */
    public class ColorProperty {
        private final String key;
        private final String description;
        private Color defaultLightValue;
        private Color defaultDarkValue;

        private Color lightValue;
        private Color darkValue;


        public ColorProperty(String key, String description, Color defaultValue) {
            this(key, description, defaultValue, defaultValue);
        }

        public ColorProperty(String key, String description, Color defaultLightValue,
                Color defaultDarkValue) {
            this.key = key;
            this.description = description;
            if (!properties.containsKey(key)) {
                this.defaultLightValue = defaultLightValue;
                this.defaultDarkValue = defaultDarkValue;
            }
        }

        public Color getCurrentColor() {
            if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isDarkMode()) {
                return getDarkValue();
            } else {
                return getLightValue();
            }
        }

        public Color getLightValue() {
            if (lightValue == null) {
                update();
            }
            return lightValue;
        }

        public void setLightValue(Color lightValue) {
            var old = this.lightValue;
            this.lightValue = lightValue;
            firePropertyChange(getKey(), old, lightValue);
        }

        public Color getDarkValue() {
            if (darkValue == null) {
                update();
            }
            return darkValue;
        }

        public void setDarkValue(Color darkValue) {
            var old = this.darkValue;
            this.darkValue = darkValue;
            firePropertyChange(getKey(), old, lightValue);
        }

        public void update() {
            Object v = properties.get(key);
            if (v == null) {
                setLightValue(defaultLightValue);
                setDarkValue(defaultDarkValue);
                return;
            }

            if (v instanceof Color c) {
                setDarkValue(c);
                setLightValue(c);
            } else if (v instanceof String s) {
                var c = fromHex(s);
                setDarkValue(c);
                setLightValue(c);
            } else if (v instanceof List<?> seq) {
                setLightValue(fromHex(seq.get(0).toString()));
                setDarkValue(fromHex(seq.get(1).toString()));
            } else {
                throw new IllegalArgumentException(
                    "Unexpected types for color " + key + " with value " + v);
            }
        }

        public Color fromObject(@Nullable Object o) {
            return fromHex(o.toString());
        }

        public String getKey() {
            return key;
        }

        public String getDescription() {
            return description;
        }

        public Color get() {
            return getCurrentColor();
        }
    }
}
