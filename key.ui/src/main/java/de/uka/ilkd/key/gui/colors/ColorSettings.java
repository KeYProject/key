/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.colors;

import java.awt.*;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Optional;
import java.util.stream.Stream;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

import org.jspecify.annotations.NullMarked;
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
@NullMarked
public class ColorSettings extends AbstractPropertiesSettings {
    public static final File SETTINGS_FILE_NEW =
        new File(PathConfig.getKeyConfigDir(), "colors.json");
    private static final Logger LOGGER = LoggerFactory.getLogger(ColorSettings.class);

    private static @Nullable ColorSettings INSTANCE;

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
            var config = new Configuration();
            for (PropertyEntry<?> entry : propertyEntries) {
                config.set(entry.getKey(), entry.value());
            }
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
    public class ColorProperty extends DefaultPropertyEntry<Color> {
        private final String description;

        public ColorProperty(String key, String description, Color defaultValue) {
            super(key, defaultValue, ColorSettings::fromHex, ColorSettings::toHex);
            this.description = description;
        }

        public String getDescription() {
            return description;
        }
    }
}
