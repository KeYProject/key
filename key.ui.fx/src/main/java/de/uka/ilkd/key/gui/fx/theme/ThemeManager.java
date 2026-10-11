/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.theme;

import java.util.concurrent.CopyOnWriteArrayList;
import java.util.prefs.Preferences;
import javafx.beans.property.ReadOnlyObjectProperty;
import javafx.beans.property.ReadOnlyObjectWrapper;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.Scene;

/**
 * Applies and switches the {@link Theme} of all registered {@link Scene}s of the JavaFX UI.
 * <p>
 * Counter-part of the FlatLaf look and feel handling in {@code MainWindow.updateLookAndFeel()}
 * of the Swing module {@code key.ui}. The theme stylesheet is tracked on each scene and replaced
 * when the theme changes, so every open window (including docking float stages) follows the
 * switch.
 */
public final class ThemeManager {

    /**
     * WP-3 (settings-config "theme persistence"): the user preference node and key under which
     * the chosen theme survives a restart (the JavaFX counterpart of Swing's
     * {@code ViewSettings.LookAndFeel} persisted look and feel; {@code key.core} must not be
     * touched, so the FX-specific theme lives in its own preference node, like the persisted
     * keystrokes and the docking layout). Declared before the {@link #INSTANCE} singleton: the
     * instance's constructor reads the persisted theme, so the preference node must already be
     * initialized when the class initializes.
     */
    private static final Preferences PREFERENCES =
        Preferences.userNodeForPackage(ThemeManager.class);
    /** the preference key holding the persisted theme name. */
    private static final String PREF_KEY = "theme";

    private static final ThemeManager INSTANCE = new ThemeManager();

    /** Property key under which the currently applied stylesheet URL is stored per scene. */
    private static final String SCENE_KEY = "key-ui.theme-stylesheet";

    /**
     * System property selecting the initial theme ({@code "light"} or {@code "dark"}, default
     * light). Also handy for UI tests running headless against Xvfb. When set, it overrides the
     * persisted theme (WP-3: the chosen theme survives restart via the user preference node
     * above — the property stays the explicit one-off override of headless UI tests).
     */
    public static final String THEME_PROPERTY = "key.fx.theme";

    private final ObservableList<Scene> scenes =
        FXCollections.observableList(new CopyOnWriteArrayList<>());

    private final ReadOnlyObjectWrapper<Theme> currentTheme =
        new ReadOnlyObjectWrapper<>(this, "theme", initialTheme());

    private ThemeManager() {
    }

    /**
     * Determines the initial theme from the persisted user preference (WP-3: the chosen theme
     * survives a restart); the {@code key.fx.theme} system property overrides it (the one-off
     * override of headless UI tests), and the default is light.
     */
    private static Theme initialTheme() {
        String property = System.getProperty(THEME_PROPERTY, "");
        if (!property.isEmpty()) {
            return Theme.DARK.name().equalsIgnoreCase(property) ? Theme.DARK : Theme.LIGHT;
        }
        return persistedTheme();
    }

    /**
     * WP-3: reads the persisted theme name; an unknown or missing entry falls back to light.
     */
    public static Theme persistedTheme() {
        return Theme.DARK.name().equalsIgnoreCase(PREFERENCES.get(PREF_KEY, ""))
                ? Theme.DARK
                : Theme.LIGHT;
    }

    /**
     * @return the global {@link ThemeManager} instance
     */
    public static ThemeManager getInstance() {
        return INSTANCE;
    }

    /**
     * Registers the given {@link Scene} with the theme manager and applies the current theme to
     * it. Use this for every top-level scene of the application (main window and floating
     * windows).
     *
     * @param scene the scene to manage
     */
    public void manage(Scene scene) {
        if (!scenes.contains(scene)) {
            scenes.add(scene);
        }
        updateScene(scene);
    }

    /**
     * @return the managed scenes (observable, so listeners can follow scene registration, e.g.
     *         the {@code ColorSettingsF} applying its CSS overrides to new scenes)
     */
    public ObservableList<Scene> getScenes() {
        return scenes;
    }

    /**
     * Applies the current theme to the given scene without registering it for later updates.
     * Handy for one-off windows (e.g. dialogs) that should follow the next programmatic theme
     * switch but are not tracked.
     *
     * @param scene the scene to style
     */
    public void style(Scene scene) {
        updateScene(scene);
    }

    /**
     * Switches the theme, updates all managed scenes and persists the choice (WP-3: the chosen
     * theme survives a restart — the View menu's Light/Dark Theme items and any other switch
     * route through this single choke point).
     *
     * @param theme the theme to activate
     */
    public void setTheme(Theme theme) {
        currentTheme.set(theme);
        PREFERENCES.put(PREF_KEY, theme.name());
        try {
            PREFERENCES.flush();
        } catch (java.util.prefs.BackingStoreException e) {
            // best effort: the theme still applies for this session
        }
        for (Scene scene : scenes) {
            updateScene(scene);
        }
    }

    /**
     * @return the currently active theme
     */
    public Theme getTheme() {
        return currentTheme.get();
    }

    /**
     * @return an observable property of the currently active theme
     */
    public ReadOnlyObjectProperty<Theme> themeProperty() {
        return currentTheme.getReadOnlyProperty();
    }

    private void updateScene(Scene scene) {
        ObservableList<String> stylesheets = scene.getStylesheets();
        Object previous = scene.getProperties().get(SCENE_KEY);
        if (previous instanceof String previousUrl) {
            stylesheets.remove(previousUrl);
        }
        String url = currentTheme.get().stylesheetUrl();
        if (!stylesheets.contains(url)) {
            stylesheets.add(url);
        }
        scene.getProperties().put(SCENE_KEY, url);
    }
}
