/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF.ContextMenuF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF.LeftPanelF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF.SettingsF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF.StartupF;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless unit test of the FX slicing provider {@link SlicingExtensionF} (MP9.4).
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the provider's contributions themselves are JavaFX widgets
 * ({@code Tab}, {@code ScrollPane}, {@code SettingsPanelF}) whose construction requires a
 * running JavaFX toolkit, so this test asserts the SPI contribution through the headless seams
 * instead: the {@code @Info} annotation, the implemented SPI sub-interfaces
 * ({@link SettingsF}, {@link LeftPanelF}, {@link ContextMenuF}, {@link StartupF}), the shared
 * settings/panel title constants and the service-loader registration. The live construction is
 * exercised by the app-run verification (gate 2, {@code key.fx.verify.extensions}).
 */
class SlicingExtensionFTest {

    private static final String SERVICE_FILE =
        "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF";

    @Test
    void infoAnnotation() {
        KeYGuiExtensionF.Info info =
            SlicingExtensionF.class.getAnnotation(KeYGuiExtensionF.Info.class);
        assertNotNull(info);
        assertEquals("Slicing", info.name());
        assertTrue(info.optional());
        assertFalse(info.experimental());
        assertEquals(9001, info.priority());
    }

    @Test
    void contributesSettingsProvider() {
        SlicingExtensionF provider = new SlicingExtensionF();
        // the provider is headless-constructible: UI widgets are created lazily
        assertTrue(provider instanceof SettingsF);
        assertEquals("Proof Slicing", SlicingSettingsProviderF.DESCRIPTION);
        assertEquals(10000, SlicingSettingsProviderF.PRIORITY_OF_SETTINGS);
    }

    @Test
    void contributesLeftPanelTab() {
        SlicingExtensionF provider = new SlicingExtensionF();
        assertTrue(provider instanceof LeftPanelF);
        assertEquals("Proof Slicing", SlicingExtensionF.getPanelTitle());
    }

    @Test
    void implementsContextMenuAndStartup() {
        SlicingExtensionF provider = new SlicingExtensionF();
        assertTrue(provider instanceof ContextMenuF);
        assertTrue(provider instanceof StartupF);
    }

    @Test
    void registeredViaServiceLoader() {
        String content = readResource(SERVICE_FILE);
        assertNotNull(content);
        assertTrue(content.lines()
                .map(String::strip)
                .anyMatch(SlicingExtensionF.class.getName()::equals));
    }

    /**
     * Reads a classpath resource (null-tolerant: returns {@code null} if absent).
     */
    private static @org.jspecify.annotations.Nullable String readResource(String name) {
        try (InputStream in =
            SlicingExtensionFTest.class.getClassLoader().getResourceAsStream(name)) {
            if (in == null) {
                return null;
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            return null;
        }
    }
}
