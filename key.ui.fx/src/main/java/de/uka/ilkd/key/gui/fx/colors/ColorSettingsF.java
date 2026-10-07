/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.colors;

import java.io.IOException;
import java.io.Writer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;
import java.util.stream.Stream;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.paint.Color;

import de.uka.ilkd.key.gui.fx.theme.Theme;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Configurable colors for KeY, counter-part of {@code de.uka.ilkd.key.gui.colors.ColorSettings}
 * of the Swing module {@code key.ui}.
 * <p>
 * If you need a new color use: {@link #define(String, String, Color, Color)}.
 * <p>
 * The settings are shared with the Swing UI via the same file ({@code colors.json} in the KeY
 * configuration directory) with the same keys and the same value format: a color is the string
 * {@code #AARRGGBB} (used for both themes) or a two-element list {@code [light, dark]} with
 * per-theme colors. Entries of keys unknown to this UI are preserved on save.
 * <p>
 * In addition to the Swing original, the user values are applied as <em>CSS property
 * overrides</em>: the keys of the mapping table {@link #CSS_VARIABLES} are written into the
 * inline style of the root nodes of all managed scenes (e.g. {@code -key-hl-java}), so they win
 * over the theme stylesheet defaults. Keys without an FX counterpart are kept in the file but
 * have no visual effect here (see {@link #CSS_VARIABLES} for the documented mapping).
 */
public final class ColorSettingsF {

    private static final Logger LOGGER = LoggerFactory.getLogger(ColorSettingsF.class);

    /** the shared settings file (the same as the Swing module's) */
    public static final Path SETTINGS_FILE = PathConfig.getSettingsFile("colors.json");

    private static ColorSettingsF INSTANCE;

    /** the raw entries of the file plus the edits made in the colors panel; written back on save */
    private final Map<String, Object> properties = new TreeMap<>();

    private final List<ColorPropertyF> propertyEntries = new ArrayList<>(64);

    private final ObjectProperty<Theme> theme =
        new SimpleObjectProperty<>(this, "theme", ThemeManager.getInstance().getTheme());

    /**
     * Mapping of the shared {@code colors.json} keys (the keys of the Swing
     * {@code ColorSettings}) to the CSS custom properties of the JavaFX themes. Keys that are
     * defined here but absent from this table are configurable in the colors panel but have no
     * FX counterpart yet:
     * <ul>
     * <li>{@code [key]*} — the .key lexer of the Swing source view; the FX source view shows
     * problem files without lexer coloring</li>
     * <li>{@code infotree.syntax.*} — the Swing rule/symbol browser (deferred in the FX UI)</li>
     * <li>{@code [SourceView]normalHighlight/mostRecentHighlight/tabHighlight/originHighlight},
     * {@code [sequentSearchBar]highlight_1/2}, {@code [currentGoal]*},
     * {@code [sequentHideWarningBorder]alert}, {@code [innerNodeView]*} — Swing paints
     * translucent background rectangles/highlight borders which the TextFlow-based FX views
     * cannot paint per-run (see the M2f report); the FX search and click highlights use text
     * colors derived from {@code -key-accent}</li>
     * <li>{@code [java]javadoc} — the FX lexer has no separate javadoc category</li>
     * <li>{@code [proofTree]gray/lightBlue/pink}, {@code [solverListener]*}, {@code javac.*} —
     * the corresponding visuals (heatmap, linked-goal tree color, SMT listener, javac
     * extension) are not ported yet</li>
     * </ul>
     */
    private static final Map<String, String> CSS_VARIABLES = Map.ofEntries(
        Map.entry("SETTINGS_TEXTFIELD_ERROR", "-key-settings-error"),
        Map.entry("[java]keyword", "-key-hl-java"),
        Map.entry("[java]comment", "-key-hl-comment"),
        Map.entry("[java]jml", "-key-hl-jml"),
        Map.entry("[java]jmlKeyword", "-key-hl-jml-keyword"),
        Map.entry("[sequentView]prop_logic_color", "-key-sequent-hl-prop"),
        Map.entry("[sequentView]dyn_logic_color", "-key-sequent-hl-dyn"),
        Map.entry("[sequentView]prog_var_color", "-key-sequent-hl-progvar"),
        Map.entry("[sequentView]sequent_arrow_color", "-key-sequent-hl-arrow"),
        Map.entry("[proofTree]darkGreen", "-key-proved"),
        Map.entry("[proofTree]darkRed", "-key-error"),
        Map.entry("[proofTree]orange", "-key-interactive"));

    private ColorSettingsF() {
        theme.addListener((obs, old, value) -> applyToScenes());
        ObservableList<Scene> scenes = ThemeManager.getInstance().getScenes();
        scenes.addListener(
            (ListChangeListener<Scene>) change -> ThemeManager.getInstance().getScenes()
                    .forEach(this::applyToScene));
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    /**
     * @return the global color settings instance, loading {@link #SETTINGS_FILE} on first access
     */
    public static ColorSettingsF getInstance() {
        if (INSTANCE == null) {
            if (Files.exists(SETTINGS_FILE)) {
                try {
                    LOGGER.info("Load color settings from file {}", SETTINGS_FILE);
                    INSTANCE = new ColorSettingsF();
                    Configuration.load(SETTINGS_FILE).getEntries()
                            .forEach(entry -> INSTANCE.properties.put(entry.getKey(),
                                entry.getValue()));
                    return INSTANCE;
                } catch (IOException e) {
                    LOGGER.error("Could not read {}", SETTINGS_FILE, e);
                }
            }
            INSTANCE = new ColorSettingsF();
            return INSTANCE;
        }
        return INSTANCE;
    }

    /**
     * Defines a new color property with per-theme defaults (Swing {@code ColorSettings.define}).
     *
     * @param key the key in {@code colors.json}
     * @param desc a human readable description
     * @param light the light theme default
     * @param dark the dark theme default
     * @return the property
     */
    public static ColorPropertyF define(String key, String desc, Color light, Color dark) {
        return getInstance().createColorProperty(key, desc, light, dark);
    }

    /**
     * Defines a new color property with one default for both themes.
     *
     * @param key the key in {@code colors.json}
     * @param desc a human readable description
     * @param color the default
     * @return the property
     */
    public static ColorPropertyF define(String key, String desc, Color color) {
        return define(key, desc, color, color);
    }

    /**
     * Converts the given RGB triple into a color with full opacity.
     *
     * @param r red 0-255
     * @param g green 0-255
     * @param b blue 0-255
     * @return the color
     */
    public static Color color(int r, int g, int b) {
        return Color.rgb(r, g, b);
    }

    /**
     * Formats a color as the shared-file string {@code #AARRGGBB} (Swing
     * {@code ColorSettings.toHex}).
     *
     * @param c the color
     * @return the hex string
     */
    public static String toHex(Color c) {
        int a = (int) Math.round(c.getOpacity() * 255);
        int r = (int) Math.round(c.getRed() * 255);
        int g = (int) Math.round(c.getGreen() * 255);
        int b = (int) Math.round(c.getBlue() * 255);
        return String.format("#%02X%02X%02X%02X", a, r, g, b);
    }

    /**
     * Formats a color for the use inside a JavaFX CSS style: {@code #RRGGBB} for opaque colors,
     * {@code #RRGGBBAA} otherwise. This is <em>not</em> the file format of {@link #toHex(Color)},
     * which encodes the alpha channel first (Swing parity).
     *
     * @param c the color
     * @return the CSS web color string
     */
    public static String toCssHex(Color c) {
        int a = (int) Math.round(c.getOpacity() * 255);
        int r = (int) Math.round(c.getRed() * 255);
        int g = (int) Math.round(c.getGreen() * 255);
        int b = (int) Math.round(c.getBlue() * 255);
        if (a >= 255) {
            return String.format("#%02X%02X%02X", r, g, b);
        }
        return String.format("#%02X%02X%02X%02X", r, g, b, a);
    }

    /**
     * Parses the shared-file color string, exactly like Swing {@code ColorSettings.fromHex}: the
     * bytes are {@code AARRGGBB}, a six-digit string therefore decodes to a transparent color.
     *
     * @param s the hex string
     * @return the color
     */
    public static Color fromHex(String s) {
        long i = Long.decode(s);
        return Color.rgb((int) ((i >> 16) & 0xFF), (int) ((i >> 8) & 0xFF), (int) (i & 0xFF),
            (int) ((i >> 24) & 0xFF) / 255.0);
    }

    /**
     * Inverts the given color (Swing {@code ColorSettings.invert}, used for text on colored
     * backgrounds).
     *
     * @param c the color
     * @return the inverted color
     */
    public static Color invert(Color c) {
        return Color.rgb(255 - (int) (c.getRed() * 255), 255 - (int) (c.getGreen() * 255),
            255 - (int) (c.getBlue() * 255));
    }

    /**
     * Writes the current settings to {@link #SETTINGS_FILE} (Swing {@code ColorSettings.save}).
     * Entries of unknown keys are preserved.
     */
    public void save() {
        LOGGER.info("Save color settings to: {}", SETTINGS_FILE.toAbsolutePath());
        try {
            Files.createDirectories(SETTINGS_FILE.getParent());
            try (Writer writer = Files.newBufferedWriter(SETTINGS_FILE)) {
                var config = new Configuration(properties);
                config.save(writer, "KeY's Colors");
                writer.flush();
            }
        } catch (IOException ex) {
            LOGGER.error("Failed to save color settings", ex);
        }
    }

    private ColorPropertyF createColorProperty(String key, String description, Color defaultLight,
            Color defaultDark) {
        Optional<ColorPropertyF> item =
            getProperties().filter(it -> it.getKey().equals(key)).findFirst();
        if (item.isPresent()) {
            return item.get();
        }
        ColorPropertyF pe = new ColorPropertyF(key, description, defaultLight, defaultDark);
        propertyEntries.add(pe);
        return pe;
    }

    /**
     * @return the defined color properties
     */
    public Stream<ColorPropertyF> getProperties() {
        return propertyEntries.stream();
    }

    /**
     * @return whether the given key has an override entry in the settings file (or was edited in
     *         the colors panel)
     */
    public boolean isOverridden(String key) {
        return properties.containsKey(key);
    }

    /**
     * Applies the overridden colors as CSS property overrides to all scenes managed by the
     * {@link ThemeManager}.
     */
    public void applyToScenes() {
        ThemeManager.getInstance().getScenes().forEach(this::applyToScene);
    }

    private void applyToScene(Scene scene) {
        Node root = scene.getRoot();
        if (root == null) {
            return;
        }
        StringBuilder style = new StringBuilder();
        Theme current = theme.get();
        for (ColorPropertyF property : propertyEntries) {
            if (!isOverridden(property.getKey())) {
                continue;
            }
            String variable = CSS_VARIABLES.get(property.getKey());
            if (variable == null) {
                continue;
            }
            Color value =
                current == Theme.DARK ? property.getDarkValue() : property.getLightValue();
            style.append(variable).append(": ").append(toCssHex(value)).append("; ");
        }
        root.setStyle(style.toString());
        LOGGER.debug("Applied color overrides to scene: {}", style);
    }

    /**
     * A property for handling colors, counter-part of the Swing
     * {@code ColorSettings.ColorProperty}.
     */
    public class ColorPropertyF {

        private final String key;
        private final String description;
        private final Color defaultLightValue;
        private final Color defaultDarkValue;

        private final ObjectProperty<Color> lightValue = new SimpleObjectProperty<>();
        private final ObjectProperty<Color> darkValue = new SimpleObjectProperty<>();

        private ColorPropertyF(String key, String description, Color defaultLightValue,
                Color defaultDarkValue) {
            this.key = key;
            this.description = description;
            this.defaultLightValue = defaultLightValue;
            this.defaultDarkValue = defaultDarkValue;
            update();
        }

        /**
         * @return the color of the current theme
         */
        public Color getCurrentColor() {
            return theme.get() == Theme.DARK ? getDarkValue() : getLightValue();
        }

        /**
         * @return the light theme color
         */
        public Color getLightValue() {
            return lightValue.get();
        }

        /**
         * @return the observable light theme color
         */
        public javafx.beans.property.ReadOnlyObjectProperty<Color> lightValueProperty() {
            return lightValue;
        }

        /**
         * Sets the light theme color and records the override (the Swing original fires a
         * property change but never persists the edit; the FX UI persists it into
         * {@code colors.json}).
         *
         * @param lightValue the light color
         */
        public void setLightValue(Color lightValue) {
            this.lightValue.set(lightValue);
            storeOverride();
            applyToScenes();
        }

        /**
         * @return the dark theme color
         */
        public Color getDarkValue() {
            return darkValue.get();
        }

        /**
         * @return the observable dark theme color
         */
        public javafx.beans.property.ReadOnlyObjectProperty<Color> darkValueProperty() {
            return darkValue;
        }

        /**
         * Sets the dark theme color and records the override.
         *
         * @param darkValue the dark color
         */
        public void setDarkValue(Color darkValue) {
            this.darkValue.set(darkValue);
            storeOverride();
            applyToScenes();
        }

        private void storeOverride() {
            Color light = lightValue.get();
            Color dark = darkValue.get();
            if (light.equals(dark)) {
                properties.put(key, toHex(light));
            } else {
                properties.put(key, List.of(toHex(light), toHex(dark)));
            }
        }

        /**
         * Re-reads the value from the settings file (Swing {@code ColorProperty.update}): a
         * string value applies to both themes, a two-element list to light and dark.
         */
        public void update() {
            Object v = properties.get(key);
            if (v == null) {
                lightValue.set(defaultLightValue);
                darkValue.set(defaultDarkValue);
                return;
            }
            if (v instanceof Color c) {
                darkValue.set(c);
                lightValue.set(c);
            } else if (v instanceof String s) {
                Color c = fromHex(s);
                darkValue.set(c);
                lightValue.set(c);
            } else if (v instanceof List<?> seq) {
                lightValue.set(fromHex(seq.get(0).toString()));
                darkValue.set(fromHex(seq.get(1).toString()));
            } else {
                throw new IllegalArgumentException(
                    "Unexpected types for color " + key + " with value " + v);
            }
        }

        /** @return the key in {@code colors.json} */
        public String getKey() {
            return key;
        }

        /** @return the human readable description */
        public String getDescription() {
            return description;
        }
    }
}
