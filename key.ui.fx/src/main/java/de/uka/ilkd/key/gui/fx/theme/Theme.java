/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.theme;

import java.util.function.Supplier;

import atlantafx.base.theme.CupertinoDark;
import atlantafx.base.theme.CupertinoLight;
import atlantafx.base.theme.Dracula;
import atlantafx.base.theme.NordDark;
import atlantafx.base.theme.NordLight;
import atlantafx.base.theme.PrimerDark;
import atlantafx.base.theme.PrimerLight;

/**
 * The visual themes of the JavaFX UI, replacing the FlatLaf look and feel choice of the Swing
 * module {@code key.ui} (Swing {@code StandardUISettings} lists the installed look and feels,
 * {@code MainWindow.updateLookAndFeel} applies the persisted one).
 * <p>
 * Every theme is a composition of two layers: the <em>AtlantaFX</em> base look applied as the
 * user-agent stylesheet (the JVM-global {@code Application.setUserAgentStylesheet} setting,
 * replacing the JavaFX default Modena look), and the KeY-specific CSS file applied as an
 * additional per-scene stylesheet by {@link ThemeManager}. The KeY layer defines the
 * {@code -key-*} palette variables consumed by the KeY components and the
 * {@code ColorSettingsF} user overrides; scene stylesheets override user-agent stylesheets in
 * the CSS cascade, so the KeY layer keeps precedence over the AtlantaFX base.
 * <p>
 * The AtlantaFX themes (3.0.0) are plain stylesheet-URL holders — instantiating one and
 * querying {@code getUserAgentStylesheet()} requires no running JavaFX toolkit, so providers
 * of this enum are toolkit-free and testable headless.
 */
public enum Theme {
    /** GitHub Primer light (AtlantaFX), KeY light layer. */
    PRIMER_LIGHT("Primer Light", PrimerLight::new, "key-light.css"),

    /** GitHub Primer dark (AtlantaFX), KeY dark layer. */
    PRIMER_DARK("Primer Dark", PrimerDark::new, "key-dark.css"),

    /** Nord light (AtlantaFX), KeY light layer. */
    NORD_LIGHT("Nord Light", NordLight::new, "key-light.css"),

    /** Nord dark (AtlantaFX), KeY dark layer. */
    NORD_DARK("Nord Dark", NordDark::new, "key-dark.css"),

    /** Cupertino light (AtlantaFX), KeY light layer. */
    CUPERTINO_LIGHT("Cupertino Light", CupertinoLight::new, "key-light.css"),

    /** Cupertino dark (AtlantaFX), KeY dark layer. */
    CUPERTINO_DARK("Cupertino Dark", CupertinoDark::new, "key-dark.css"),

    /** Dracula (AtlantaFX, dark only), KeY dark layer. */
    DRACULA("Dracula", Dracula::new, "key-dark.css");

    /** the name of the dark KeY layer CSS file (the light/dark decision of a theme). */
    private static final String DARK_STYLESHEET = "key-dark.css";

    /** the human-readable label shown in the theme picker (View > Theme, settings panel). */
    private final String displayName;

    /**
     * lazily creates the AtlantaFX theme and returns its user-agent stylesheet path; a
     * {@code Supplier<String>} avoids referencing the {@code atlantafx.base.theme.Theme} type,
     * which would clash with this enum's simple name.
     */
    private final Supplier<String> userAgentStylesheet;

    /** the KeY-specific CSS layer applied per scene (see class javadoc). */
    private final String stylesheet;

    Theme(String displayName, Supplier<? extends atlantafx.base.theme.Theme> theme,
            String stylesheet) {
        this.displayName = displayName;
        this.userAgentStylesheet = () -> theme.get().getUserAgentStylesheet();
        this.stylesheet = stylesheet;
    }

    /**
     * @return the human-readable label shown in the theme picker (View > Theme submenu and the
     *         settings panel)
     */
    public String displayName() {
        return displayName;
    }

    /**
     * The user-agent stylesheet path of the AtlantaFX base look ({@code
     * /atlantafx/base/theme/&lt;name&gt;.css}), to be applied via {@code
     * Application.setUserAgentStylesheet} (toolkit-free, the path is a plain constant).
     *
     * @return the user-agent stylesheet path
     */
    public String atlantaUserAgentStylesheet() {
        return userAgentStylesheet.get();
    }

    /**
     * @return the resource URL of the KeY CSS layer (relative to this class)
     */
    public String stylesheetUrl() {
        return Theme.class.getResource(stylesheet).toExternalForm();
    }

    /** @return whether this is a dark theme (dark AtlantaFX look, dark KeY layer) */
    public boolean isDark() {
        return stylesheet.equals(DARK_STYLESHEET);
    }

    /**
     * Parses a persisted or property theme value: the legacy two-value entries of the
     * pre-AtlantaFX UI ({@code LIGHT}/{@code DARK}, e.g. an existing user preference or the
     * {@code key.fx.theme} override of headless UI tests) map to the Primer pair, otherwise the
     * enum name matches case-insensitively; an unknown or empty value falls back to
     * {@link #PRIMER_LIGHT} (the previous default).
     *
     * @param value the stored value, may be empty
     * @return the theme, never {@code null}
     */
    public static Theme parse(String value) {
        if ("LIGHT".equalsIgnoreCase(value)) {
            return PRIMER_LIGHT;
        }
        if ("DARK".equalsIgnoreCase(value)) {
            return PRIMER_DARK;
        }
        for (Theme theme : values()) {
            if (theme.name().equalsIgnoreCase(value)) {
                return theme;
            }
        }
        return PRIMER_LIGHT;
    }
}
