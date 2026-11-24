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
import static org.assertj.core.api.Assertions.assertThatCode;

/**
 * Toolkit-free tests of the FX port of the Swing LogView extension ({@link LogViewExtensionF}):
 * the service-loaded provider declares the Swing {@code KeYGuiExtension.Info} of {@code
 * de.uka.ilkd.key.gui.LogView} (LogView.java:37: experimental=false, name="Log View"; optional
 * is undeclared and defaults to false in both SPIs), implements the Swing {@code StatusLine}
 * capability only, is instantiable without a running JavaFX toolkit, and is registered in the
 * service-loader file.
 * <p>
 * KNOWN-SIMPLIFIED: JavaFX 25 requires a running FX toolkit to even <em>construct</em> a
 * control (e.g. {@code new Button(...)} fails headless with "Toolkit not initialized"), and
 * this repo's unit tests run without a display and without a headless glass platform. The
 * button surface (the BOOK icon at size 16, the "Show log" tooltip, the open action) is
 * therefore verified by the in-app {@code key.fx.verify.*} hooks instead of by unit tests; this
 * is why {@link LogViewExtensionF} creates its status-line button lazily in
 * {@code getStatusLineControls()}.
 */
class LogViewExtensionFTest {

    @Test
    void infoAnnotationMirrorsTheSwingLogView() {
        KeYGuiExtensionF.Info info = LogViewExtensionF.class
                .getAnnotation(KeYGuiExtensionF.Info.class);
        assertThat(info).isNotNull();
        // Swing @KeYGuiExtension.Info(experimental = false, name = "Log View"), LogView.java:37
        assertThat(info.name()).isEqualTo("Log View");
        assertThat(info.experimental()).isFalse();
        assertThat(info.optional()).isFalse();
    }

    @Test
    void providerImplementsTheSwingStatusLineCapabilityOnly() {
        LogViewExtensionF extension = new LogViewExtensionF();
        // Swing LogView implements KeYGuiExtension + KeYGuiExtension.StatusLine (LogView.java:38)
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.StatusLineF.class);
        // ... and no other capability (the Swing original declares none either)
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.MainMenuF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.ToolbarF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.LeftPanelF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.ContextMenuF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.SettingsF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.TooltipF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.KeyboardShortcutsF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.StartupF.class);
    }

    @Test
    void providerIsInstantiableWithoutFxToolkit() {
        // the status-line button is created lazily inside getStatusLineControls — never in the
        // constructor or a field initializer — so headless instantiation must not throw
        assertThatCode(LogViewExtensionF::new).doesNotThrowAnyException();
    }

    @Test
    void serviceRegistrationNamesTheProvider() throws IOException {
        try (InputStream in = LogViewExtensionFTest.class.getClassLoader()
                .getResourceAsStream(
                    "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF")) {
            assertThat(in).as("service-loader file on the classpath").isNotNull();
            String content = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            assertThat(content)
                    .contains("de.uka.ilkd.key.gui.fx.extension.contrib.LogViewExtensionF");
        }
    }
}
