/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Toolkit-free tests of the FX port of the JML enabled-keys indicator
 * ({@link JmlEnabledKeysIndicatorF}, Swing {@code de.uka.ilkd.key.gui.JmlEnabledKeysIndicator}):
 * the provider is constructible headless, declares the Swing {@code @KeYGuiExtension.Info} surface
 * (JmlEnabledKeysIndicator.java:21), observes the global general-settings singleton
 * (JmlEnabledKeysIndicator.java:23-24) and is registered in the service-loader file.
 * <p>
 * KNOWN-SIMPLIFIED: JavaFX 25 requires a running FX toolkit to even <em>construct</em> a control
 * (e.g. {@code new Label()} fails headless with "Toolkit not initialized"), and this repo's unit
 * tests run without a display and without a headless glass platform. The control-level SPI
 * contract (the status-line label itself, its text/visibility updates on
 * {@code GeneralSettings.KEY_JML_ENABLED_KEYS}) is therefore verified by the in-app
 * {@code key.fx.verify.extensions} hook instead of by unit tests; the unit tests cover the
 * toolkit-free surface only — this is why {@link JmlEnabledKeysIndicatorF} creates its label
 * lazily (see {@code CachingExtensionFTest} in {@code keyext.caching.fx} for the same design).
 */
class JmlEnabledKeysIndicatorFTest {

    private final JmlEnabledKeysIndicatorF extension = new JmlEnabledKeysIndicatorF();

    @Test
    void infoAnnotationMirrorsTheSwingInfo() {
        // Swing JmlEnabledKeysIndicator.java:21: @Info(experimental = false,
        // name = "JML Enabled Keys Indicator for the Status Line") — optional defaults to false
        KeYGuiExtensionF.Info info = JmlEnabledKeysIndicatorF.class
                .getAnnotation(KeYGuiExtensionF.Info.class);
        assertThat(info).isNotNull();
        assertThat(info.name()).isEqualTo("JML Enabled Keys Indicator for the Status Line");
        assertThat(info.optional()).isFalse();
        assertThat(info.experimental()).isFalse();
    }

    @Test
    void providerImplementsPortableCapabilities() {
        // the provider itself is constructible headless (no FX toolkit required)
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.StatusLineF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.StartupF.class);
    }

    @Test
    void indicatorObservesTheGeneralSettingsSingleton() {
        // Swing JmlEnabledKeysIndicator.java:23-24: the observed settings object is
        // ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
        assertThat(extension.settings())
                .isSameAs(ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings());
    }

    @Test
    void serviceRegistrationNamesTheProvider() throws IOException {
        try (InputStream in = JmlEnabledKeysIndicatorFTest.class.getClassLoader()
                .getResourceAsStream(
                    "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF")) {
            assertThat(in).as("service-loader file on the classpath").isNotNull();
            String content = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            assertThat(content)
                    .contains("de.uka.ilkd.key.gui.fx.extension.contrib.JmlEnabledKeysIndicatorF");
        }
    }
}
