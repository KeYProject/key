/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless unit test of the {@link TestgenExtensionF} provider (MP9.5, WP-7): the {@code @Info}
 * annotation, the compilable SPI capability surface ({@link KeYGuiExtensionF.MainMenuF} +
 * {@link KeYGuiExtensionF.SettingsF} + {@link KeYGuiExtensionF.ToolbarF} +
 * {@link KeYGuiExtensionF.StartupF}) and the reflection-dispatched settings entry (a {@code
 * SettingsProviderF} proxy whose {@code getPanel/apply} forward the main window to the extension).
 * <p>
 * <b>KNOWN-SIMPLIFIED (headless):</b> every {@code javafx.scene.control.Control} triggers the FX
 * toolkit in its class initializer ("Toolkit not initialized"), and this module's
 * {@code build.gradle} exposes no headless toolkit to the tests — so the toolbar {@code Button}s,
 * the "Test Case Generation" menu and the settings-panel {@code CheckBox}/spinner widgets are
 * built lazily inside the running app only, and the test asserts the provider/capability surface
 * instead of the control trees. Neither the provider construction nor the capability asserts
 * touch the JavaFX toolkit; the run dialogs and the generation workers are deliberately not
 * exercised here.
 */
class TestgenExtensionFTest {

    @Test
    void providerInfoAnnotation() {
        KeYGuiExtensionF extension = new TestgenExtensionF();
        KeYGuiExtensionF.Info info =
            extension.getClass().getAnnotation(KeYGuiExtensionF.Info.class);
        assertNotNull(info, "the provider must carry the @KeYGuiExtensionF.Info annotation");
        assertEquals("Test case generation", info.name());
        assertEquals("key.testgen (JavaFX port): generate JUnit test cases from the current "
            + "proof, or search for a counterexample, using the Z3 CE solver.",
            info.description());
        assertFalse(info.experimental(), "the Swing original is not experimental");
        assertFalse(info.optional());
    }

    @Test
    void capabilitySurface() {
        KeYGuiExtensionF extension = new TestgenExtensionF();
        // WP-7 — the Swing capability set (main menu, toolbar, Startup hook, settings panel) is
        // complete; the two toolbar Buttons and the control trees are built lazily in the app
        // (they need the FX toolkit).
        assertInstanceOf(KeYGuiExtensionF.MainMenuF.class, extension,
            "Test Generation menu with the two Swing menu actions");
        assertInstanceOf(KeYGuiExtensionF.SettingsF.class, extension,
            "TestgenOptionsPanel port");
        assertInstanceOf(KeYGuiExtensionF.ToolbarF.class, extension,
            "the two plain action buttons of the Swing JToolBar");
        assertInstanceOf(KeYGuiExtensionF.StartupF.class, extension,
            "Swing Startup hook: window capture at app startup");
    }

    @Test
    void settingsProviderDispatch() {
        TestgenExtensionF extension = new TestgenExtensionF();
        var settings = extension.getSettings();
        assertNotNull(settings);
        assertEquals("TestGen", settings.getDescription(),
            "Swing TestgenOptionsPanel.getDescription");
        assertEquals(0, settings.getPriorityOfSettings());
        assertTrue(settings.getChildProviders().isEmpty());
        assertTrue(settings.contains("gen"), "description substring search");
        assertFalse(settings.contains("proof management"));
    }
}
