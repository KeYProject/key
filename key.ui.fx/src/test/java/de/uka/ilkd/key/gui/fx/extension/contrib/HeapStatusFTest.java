/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Toolkit-free tests of the FX port of the heap-status extension ({@link HeapStatusF}): the
 * service-loaded provider declares its {@link KeYGuiExtensionF.Info} exactly like the Swing
 * original (name "Heap-Indicator", the description, experimental=false, optional=false),
 * implements the StatusLineF capability (and no other — the Swing
 * {@code de.uka.ilkd.key.gui.utilities.HeapStatusExt} implements only
 * {@code KeYGuiExtension.StatusLine}, HeapStatusExt.java:32), and is registered in the
 * service-loader file.
 * <p>
 * KNOWN-SIMPLIFIED: JavaFX 25 requires a running FX toolkit to even <em>construct</em> a control
 * (e.g. {@code new ProgressBar(...)} fails headless with "Toolkit not initialized"), and this
 * repo's unit tests run without a display; the control-level behavior (bar value/string/tooltip,
 * click-to-GC, "Open JConsole"/"Run Gc" context menu, the periodic 5-second refresh lifecycle) is
 * therefore not covered here — the provider is instantiated headless (its status-line control is
 * created lazily inside {@link HeapStatusF#getStatusLineControls()}, which the host calls on the
 * FX thread), mirroring the test design of {@code keyext.caching.fx CachingExtensionFTest}; the
 * control surface is exercised by the in-app {@code key.fx.verify.extensions} hook.
 */
class HeapStatusFTest {

    private final HeapStatusF extension = new HeapStatusF();

    @Test
    void infoAnnotationDeclaresHeapIndicator() {
        KeYGuiExtensionF.Info info = HeapStatusF.class
                .getAnnotation(KeYGuiExtensionF.Info.class);
        assertThat(info).isNotNull();
        assertThat(info.name()).isEqualTo("Heap-Indicator");
        assertThat(info.description()).isEqualTo(
            "Shows an indication of the current heap consumption in the status line of key");
        assertThat(info.experimental()).isFalse();
        assertThat(info.optional()).isFalse();
    }

    @Test
    void providerImplementsOnlyTheStatusLineCapability() {
        // the provider itself is constructible headless (no FX toolkit required)
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.StatusLineF.class);
        // Swing HeapStatusExt implements only KeYGuiExtension.StatusLine (HeapStatusExt.java:32)
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.MainMenuF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.ToolbarF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.LeftPanelF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.ContextMenuF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.SettingsF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.StartupF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.TooltipF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.KeyboardShortcutsF.class);
    }

    @Test
    void serviceRegistrationNamesTheProvider() throws IOException {
        try (InputStream in = HeapStatusFTest.class.getClassLoader()
                .getResourceAsStream(
                    "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF")) {
            assertThat(in).as("service-loader file on the classpath").isNotNull();
            String content = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            assertThat(content)
                    .contains("de.uka.ilkd.key.gui.fx.extension.contrib.HeapStatusF");
        }
    }
}
