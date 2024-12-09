/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.colors;

import java.awt.*;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Objects;
import java.util.Optional;
import java.util.Properties;
import java.util.stream.Stream;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

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
public class ColorSettings extends AbstractPropertiesSettings {
    public static final File SETTINGS_FILE_NEW =
        new File(PathConfig.getKeyConfigDir(), "colors.json");
    private static final Logger LOGGER = LoggerFactory.getLogger(ColorSettings.class);
    private static ColorSettings INSTANCE;

    public ColorSettings(Configuration load) {
        super("");
        readSettings(load);
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    public static ColorSettings getInstance() {
        if (INSTANCE == null) {
            if (SETTINGS_FILE_NEW.exists()) {
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
        return getInstance().createColorProperty(key, desc, color);
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
        LOGGER.info("Save color settings to: {}", SETTINGS_FILE_NEW.getAbsolutePath());
        try (Writer writer = new FileWriter(SETTINGS_FILE_NEW)) {
            var config = new Configuration(properties);
            config.save(writer, "KeY's Colors");
            writer.flush();
        } catch (IOException ex) {
            LOGGER.error("Failed to save color settings", ex);
        }
    }

    private ColorProperty createColorProperty(String key, String description, Color defaultValue) {
        Optional<ColorProperty> item =
            getProperties().filter(it -> it.getKey().equals(key)).findFirst();
        if (item.isPresent()) {
            return item.get();
        }

        ColorProperty pe = new ColorProperty(key, description, defaultValue);
        propertyEntries.add(pe);
        return pe;
    }

    public Stream<ColorProperty> getProperties() {
        return propertyEntries.stream().map(ColorProperty.class::cast);
    }

    /**
     * A property for handling colors.
     */
    public class ColorProperty implements PropertyEntry<Color> {
        private final String key;
        private final String description;
        private Color currentValue;

        public ColorProperty(String key, String description, Color defaultValue) {
            this.key = key;
            this.description = description;
            if (!properties.containsKey(key)) {
                set(defaultValue);
            }
        }

        @Override
        public String value() {
            if (currentValue != null) {
                return toHex(currentValue);
            }

            String v = properties.get(key).toString();

            try {
                return v;
            } catch (NumberFormatException e) {
                return toHex(Color.MAGENTA);
            }
        }

        @Override
        public Color fromObject(@Nullable Object o) {
            return fromHex(o.toString());
        }

        @Override
        public void parseFrom(String v) {
            final var old = value();
            if (!Objects.equals(old, v)) {
                currentValue = fromHex(v);
                properties.put(getKey(), v);
                firePropertyChange(getKey(), old, currentValue);
            }
        }

        @Override
        public String getKey() {
            return key;
        }

        @Override
        public void set(Color value) {
            if (currentValue != value) {
                var old = currentValue;
                currentValue = value;
                properties.put(getKey(), toHex(value));
                firePropertyChange(getKey(), old, value);
            }
        }

        @Override
        public Color get() {
            if (currentValue != null) {
                return currentValue;
            }

            String v = (String) properties.get(key);

            try {
                return currentValue = fromHex(v);
            } catch (NumberFormatException e) {
                LOGGER.error("Failed to parse color, using magenta", e);
                return Color.MAGENTA;
            }
        }

        public String getDescription() {
            return description;
        }
    }

    @Override
    public void readSettings(Properties props) {
        props.forEach((k, v) -> this.properties.put(k.toString(), v));
    }
}
