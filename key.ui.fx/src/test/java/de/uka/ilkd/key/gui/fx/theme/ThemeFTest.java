/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.theme;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Toolkit-free tests of the AtlantaFX-backed theme model ({@link Theme}): the seven themes of
 * AtlantaFX 3.0.0 pair the base look (applied as the user-agent stylesheet, a plain
 * classpath-path constant — instantiating an AtlantaFX theme requires no running JavaFX
 * toolkit) with the KeY CSS layer (light or dark) and a display name for the theme picker; the
 * legacy two-value entries of the pre-AtlantaFX UI ({@code LIGHT}/{@code DARK}) parse to the
 * Primer pair, unknown values fall back to {@link Theme#PRIMER_LIGHT}.
 */
class ThemeFTest {

    @Test
    void sevenThemesCarryTheAtlantaFXUserAgentStylesheets() {
        assertThat(Theme.values()).hasSize(7);
        assertThat(Theme.PRIMER_LIGHT.atlantaUserAgentStylesheet())
                .isEqualTo("/atlantafx/base/theme/primer-light.css");
        assertThat(Theme.PRIMER_DARK.atlantaUserAgentStylesheet())
                .isEqualTo("/atlantafx/base/theme/primer-dark.css");
        assertThat(Theme.NORD_LIGHT.atlantaUserAgentStylesheet())
                .isEqualTo("/atlantafx/base/theme/nord-light.css");
        assertThat(Theme.NORD_DARK.atlantaUserAgentStylesheet())
                .isEqualTo("/atlantafx/base/theme/nord-dark.css");
        assertThat(Theme.CUPERTINO_LIGHT.atlantaUserAgentStylesheet())
                .isEqualTo("/atlantafx/base/theme/cupertino-light.css");
        assertThat(Theme.CUPERTINO_DARK.atlantaUserAgentStylesheet())
                .isEqualTo("/atlantafx/base/theme/cupertino-dark.css");
        assertThat(Theme.DRACULA.atlantaUserAgentStylesheet())
                .isEqualTo("/atlantafx/base/theme/dracula.css");
    }

    @Test
    void everyThemeShipsItsKeyCssLayer() {
        for (Theme theme : Theme.values()) {
            assertThat(theme.stylesheetUrl())
                    .as("KeY CSS layer of %s", theme).isNotBlank();
        }
    }

    @Test
    void lightAndDarkClassification() {
        assertThat(Theme.PRIMER_LIGHT.isDark()).isFalse();
        assertThat(Theme.NORD_LIGHT.isDark()).isFalse();
        assertThat(Theme.CUPERTINO_LIGHT.isDark()).isFalse();
        assertThat(Theme.PRIMER_DARK.isDark()).isTrue();
        assertThat(Theme.NORD_DARK.isDark()).isTrue();
        assertThat(Theme.CUPERTINO_DARK.isDark()).isTrue();
        // Dracula has no light variant; it uses the dark KeY layer
        assertThat(Theme.DRACULA.isDark()).isTrue();
    }

    @Test
    void displayNamesAreThePickerLabels() {
        assertThat(Theme.PRIMER_LIGHT.displayName()).isEqualTo("Primer Light");
        assertThat(Theme.DRACULA.displayName()).isEqualTo("Dracula");
    }

    @Test
    void legacyLightAndDarkValuesMapToThePrimerPair() {
        assertThat(Theme.parse("LIGHT")).isEqualTo(Theme.PRIMER_LIGHT);
        assertThat(Theme.parse("light")).isEqualTo(Theme.PRIMER_LIGHT);
        assertThat(Theme.parse("DARK")).isEqualTo(Theme.PRIMER_DARK);
        assertThat(Theme.parse("dark")).isEqualTo(Theme.PRIMER_DARK);
    }

    @Test
    void enumNamesParseCaseInsensitively() {
        assertThat(Theme.parse("PRIMER_DARK")).isEqualTo(Theme.PRIMER_DARK);
        assertThat(Theme.parse("nord_dark")).isEqualTo(Theme.NORD_DARK);
        assertThat(Theme.parse("CupertinoLight")).isNotEqualTo(Theme.CUPERTINO_LIGHT);
        assertThat(Theme.parse("CUPERTINO_LIGHT")).isEqualTo(Theme.CUPERTINO_LIGHT);
    }

    @Test
    void unknownOrEmptyValuesFallBackToPrimerLight() {
        assertThat(Theme.parse("")).isEqualTo(Theme.PRIMER_LIGHT);
        assertThat(Theme.parse("solarized")).isEqualTo(Theme.PRIMER_LIGHT);
    }
}
