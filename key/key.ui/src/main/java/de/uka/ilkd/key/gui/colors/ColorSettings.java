package de.uka.ilkd.key.gui.colors;

import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.settings.AbstractPropertiesSettings;
import de.uka.ilkd.key.settings.PathConfig;

import java.awt.*;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Objects;
import java.util.Properties;
import java.util.stream.Stream;

/**
 * Configurable colors for KeY.
 * <p>
 * If you need a new color use: {@link #define(String, String, Color)}.
 *
 * @author Alexander Weigl
 * @version 1 (10.05.19)
 */
public class ColorSettings extends AbstractPropertiesSettings {
    public static final String SETTINGS_FILENAME = "colors.properties";
    public static final File SETTINGS_FILE = new File(PathConfig.getKeyConfigDir(), SETTINGS_FILENAME);
    private static ColorSettings INSTANCE;

    private ColorSettings(Properties settings) {
        readSettings(settings);
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    public static ColorSettings getInstance() {
        if (INSTANCE == null)
            INSTANCE = new ColorSettings(SettingsManager.loadProperties(SETTINGS_FILE));
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
        Long i = Long.decode(s);
        return new Color(
                (int) ((i >> 16) & 0xFF),
                (int) ((i >> 8) & 0xFF),
                (int) (i & 0xFF),
                (int) ((i >> 24) & 0xFF));
    }

    public static Color invert(Color c) {
        return new Color(255 - c.getRed(), 255 - c.getGreen(), 255 - c.getBlue());
    }

    /**
     * Writes the current settings to default location.
     * @see #SETTINGS_FILE
     */
    public void save() {
        System.out.println("[ColorSettings] Save color settings to: " + SETTINGS_FILE.getAbsolutePath());
        try (Writer writer = new FileWriter(SETTINGS_FILE)) {
            properties.store(writer, "KeY's Colors");
            writer.flush();
        } catch (IOException ex) {
            ex.printStackTrace();
        }
    }

    private ColorProperty createColorProperty(String key,
                                              String description,
                                              Color defaultValue) {
        ColorProperty pe = new ColorProperty(key, description, defaultValue);
        propertyEntries.add(pe);
        return pe;
    }

    public Stream<ColorProperty> getProperties() {
        return propertyEntries.stream().map(it -> (ColorProperty) it);
    }

    /**
     * A property for handling colors.
     */
    public class ColorProperty implements PropertyEntry<Color> {
        private final String key, description;
        private Color currentValue;

        public ColorProperty(String key, String description, Color defaultValue) {
            this.key = key;
            this.description = description;
            if (!properties.contains(key)) {
                set(defaultValue);
            }
        }

        @Override
        public String value() {
            if (currentValue != null)
                return toHex(currentValue);

            String v = properties.getProperty(key);

            try {
                return v;
            } catch (NumberFormatException e) {
                return toHex(Color.MAGENTA);
            }
        }

        @Override
        public void set(String v) {
            if (!Objects.equals(value(), v)) {
                currentValue = fromHex(v);
                properties.setProperty(getKey(), v);
                fireSettingsChange();
            }
        }

        @Override
        public String getKey() {
            return key;
        }

        @Override
        public void set(Color value) {
            if (currentValue != value) {
                currentValue = value;
                properties.setProperty(getKey(), toHex(value));
                fireSettingsChange();
            }
        }

        @Override
        public Color get() {
            if (currentValue != null)
                return currentValue;

            String v = properties.getProperty(key);

            try {
                return currentValue = fromHex(v);
            } catch (NumberFormatException e) {
                e.printStackTrace();
                return Color.MAGENTA;
            }
        }

        public String getDescription() {
            return description;
        }
    }
}
