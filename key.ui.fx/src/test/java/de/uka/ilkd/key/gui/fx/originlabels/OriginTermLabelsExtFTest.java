/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.originlabels;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.pp.PosInSequent;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatCode;

/**
 * Toolkit-free tests of the FX port of the origin-tracking extension ({@link
 * OriginTermLabelsExtF}, the counterpart of the Swing {@code
 * de.uka.ilkd.key.gui.originlabels.OriginTermLabelsExt}): the service-loaded provider declares
 * the Swing-parity {@link KeYGuiExtensionF.Info}, implements the portable SPI capabilities
 * (MainMenuF/ContextMenuF/TooltipF/TermInfoF — the Swing original's capability set), guards the
 * null cases of the context and term-info contributions, and keeps the View-menu nesting
 * decision of the port. JavaFX controls are created lazily inside the getters (see the
 * {@code CachingExtensionF} note), so the provider is constructible headless; the control-level
 * contracts are verified by the in-app extension verification instead (see
 * {@code CachingExtensionFTest} for the same rationale).
 */
class OriginTermLabelsExtFTest {

    private final OriginTermLabelsExtF extension = new OriginTermLabelsExtF();

    @Test
    void infoAnnotationMirrorsTheSwingOriginal() {
        // Swing OriginTermLabelsExt.java:36-37
        KeYGuiExtensionF.Info info = OriginTermLabelsExtF.class
                .getAnnotation(KeYGuiExtensionF.Info.class);
        assertThat(info).isNotNull();
        assertThat(info.name()).isEqualTo("Origin Tracking");
        assertThat(info.description()).isEqualTo("UI support for origin tracking");
        assertThat(info.optional()).isTrue();
        assertThat(info.experimental()).isFalse();
        assertThat(info.priority()).isZero();
    }

    @Test
    void providerImplementsTheSwingCapabilitySet() {
        // the provider itself is constructible headless (no FX toolkit required)
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.MainMenuF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.ContextMenuF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.TooltipF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.TermInfoF.class);
        // the Swing original implements no further capability (OriginTermLabelsExt.java:38-39)
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.ToolbarF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.StatusLineF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.LeftPanelF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.SettingsF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.KeyboardShortcutsF.class);
        assertThat(extension).isNotInstanceOf(KeYGuiExtensionF.StartupF.class);
    }

    @Test
    void mainMenuNestsUnderTheViewMenu() {
        // the porting decision: the Swing KeyAction.PATH "Origin Tracking" creates a new
        // top-level menu bar menu (ToggleTermOriginTrackingAction.java:40); the FX port nests
        // under the built-in View menu to absorb the legacy OriginLabelsF.install wiring
        assertThat(extension.getMenuPath()).isEqualTo("View");
    }

    @Test
    void contextItemsGuardNulls() {
        // null mediator/position/node must yield no items and never touch the FX toolkit
        assertThatCode(() -> extension.getSequentContextItems(null, null, null))
                .doesNotThrowAnyException();
        assertThat(extension.getSequentContextItems(null, null, null)).isEmpty();
        assertThat(extension.getProofTreeContextItems(null, null)).isEmpty();
    }

    @Test
    void termInfoAndTooltipGuardNulls() {
        // OriginTermLabel.getOrigin(PosInSequent) is null-safe (OriginTermLabel.java:79-85), so
        // the status-line info of a null position is empty; the tooltip of the whole-sequent
        // position (or of no position) contributes nothing, like the Swing original
        // (OriginTermLabelsExt.java:100-102)
        assertThat(extension.getTermInfoStrings(null, null)).isEmpty();
        assertThat(extension.getTooltipStrings(null, null)).isEmpty();
        assertThat(extension.getTooltipStrings(new KeYMediatorF(), PosInSequent.createSequentPos()))
                .isEmpty();
    }

    @Test
    void termLabelPriorityIsTheSwingDefault() {
        // Swing KeYGuiExtension.TermInfo.getTermLabelPriority default
        // (KeYGuiExtension.java:265-267)
        assertThat(extension.getTermLabelPriority()).isZero();
    }

    @Test
    void serviceRegistrationNamesTheProvider() throws IOException {
        try (InputStream in = OriginTermLabelsExtFTest.class.getClassLoader()
                .getResourceAsStream(
                    "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF")) {
            assertThat(in).as("service-loader file on the classpath").isNotNull();
            String content = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            assertThat(content)
                    .contains("de.uka.ilkd.key.gui.fx.originlabels.OriginTermLabelsExtF");
        }
    }
}
