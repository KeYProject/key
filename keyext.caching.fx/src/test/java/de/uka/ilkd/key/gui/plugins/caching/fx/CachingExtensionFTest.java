/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatCode;

/**
 * Toolkit-free tests of the FX port of the proof-caching extension ({@link CachingExtensionF}):
 * the service-loaded provider declares its {@link KeYGuiExtensionF.Info}, implements the
 * portable SPI capabilities, guards the null cases of the sequent context-menu contribution
 * (the "must never break the term menu" guarantee), and the FX-module-owned caching settings
 * singleton is registered into the global {@link ProofIndependentSettings}.
 * <p>
 * KNOWN-SIMPLIFIED: JavaFX 25 requires a running FX toolkit to even <em>construct</em> a
 * control (e.g. {@code new ToggleButton(...)} fails headless with "Toolkit not initialized"),
 * and this repo's unit tests run without a display and without a headless glass platform. The
 * control-level SPI contracts (menu/toolbar/status-line items, settings panel widget tree) are
 * therefore verified by Gate 2's in-app extension verification instead of by unit tests; the
 * unit tests cover the toolkit-free surface only. This is why {@link CachingExtensionF} creates
 * its JavaFX controls lazily (see {@code CachingExtensionF.menuToggleItem()} etc.).
 */
class CachingExtensionFTest {

    private final CachingExtensionF extension = new CachingExtensionF();

    @Test
    void infoAnnotationDeclaresProofCaching() {
        KeYGuiExtensionF.Info info = CachingExtensionF.class
                .getAnnotation(KeYGuiExtensionF.Info.class);
        assertThat(info).isNotNull();
        assertThat(info.name()).isEqualTo("Proof Caching");
        assertThat(info.optional()).isTrue();
        assertThat(info.experimental()).isFalse();
    }

    @Test
    void providerImplementsPortableCapabilities() {
        // the provider itself is constructible headless (no FX toolkit required)
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.MainMenuF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.ToolbarF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.StatusLineF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.ContextMenuF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.SettingsF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.StartupF.class);
    }

    @Test
    void sequentContextItemsGuardNulls() {
        // null goal/mediator/position must yield no items (never crash the term menu — the
        // verify hook builds its MenuContext with a null position)
        assertThat(extension.getSequentContextItems(null, null, null)).isEmpty();
    }

    @Test
    void cachingSettingsSingletonIsRegisteredAndReused() {
        // KNOWN-SIMPLIFIED singleton ownership: the FX module owns the ProofCachingSettings
        // instance (the Swing keyext CachingSettingsProvider is not on the FX compile path).
        ProofCachingSettings first = CachingSettingsProviderF.getCachingSettings();
        ProofCachingSettings second = CachingSettingsProviderF.getCachingSettings();
        assertThat(first).isSameAs(second);
        // Swing defaults (ProofCachingSettings.java:37-48: enabled=true, copy on dispose/prune)
        assertThat(first.getEnabled()).isTrue();
        assertThat(first.getDispose()).isEqualTo(ProofCachingSettings.DISPOSE_COPY);
        assertThat(first.getPrune()).isEqualTo(ProofCachingSettings.PRUNE_COPY);
        // registering the shared instance into the global settings registry is idempotent
        // (ProofIndependentSettings.addSettings, key.core) and must never throw
        assertThatCode(() -> ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(first))
                .doesNotThrowAnyException();
        // the extension reads the exact same instance (its field is initialized from the
        // module-owned singleton)
        assertThat(extension.settings()).isSameAs(first);
        assertThatCode(extension::getProofCachingEnabled).doesNotThrowAnyException();
    }

    @Test
    void serviceRegistrationNamesTheProvider() throws IOException {
        try (InputStream in = CachingExtensionFTest.class.getClassLoader()
                .getResourceAsStream(
                    "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF")) {
            assertThat(in).as("service-loader file on the classpath").isNotNull();
            String content = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            assertThat(content)
                    .contains("de.uka.ilkd.key.gui.plugins.caching.fx.CachingExtensionF");
        }
    }
}
