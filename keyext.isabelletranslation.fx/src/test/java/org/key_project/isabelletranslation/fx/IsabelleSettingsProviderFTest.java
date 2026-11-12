/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.fx;

import javafx.application.Platform;

import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The {@link SettingsProviderF} surface of the Isabelle translation extension (MP9.3).
 * <p>
 * Unlike {@link IsabelleTranslationExtensionFTest} this class <b>does</b> need the JavaFX
 * toolkit, because resolving the settings contribution instantiates the settings panel (a
 * JavaFX {@code Control}). The toolkit is started once with software rendering and no window;
 * on CI runners without a display (headless ubuntu/windows agents) {@link Platform#startup}
 * fails and the class is <em>skipped</em> via JUnit assumptions instead of failing — the panel
 * surface itself is covered in-app by the {@code key.fx.verify.extensions} hook.
 */
class IsabelleSettingsProviderFTest {

    @BeforeAll
    static void initFx() {
        try {
            Platform.startup(() -> {
            });
            Platform.setImplicitExit(false);
        } catch (IllegalStateException e) {
            // the platform is already running (e.g. a shared test JVM)
        } catch (RuntimeException e) {
            // no DISPLAY / headless CI runner — the FX toolkit cannot start
            Assumptions.assumeTrue(false,
                "FX toolkit unavailable (" + e + ") — settings-panel assertions skipped");
        }
    }

    @Test
    void settingsContribution() {
        IsabelleTranslationExtensionF extension = new IsabelleTranslationExtensionF();
        SettingsProviderF settings = extension.getSettings();
        assertNotNull(settings, "the extension must contribute a settings provider");
        assertTrue(settings instanceof IsabelleSettingsProviderF,
            "the provider must be the FX settings panel");
        assertEquals("Isabelle Translation", settings.getDescription());
    }
}
