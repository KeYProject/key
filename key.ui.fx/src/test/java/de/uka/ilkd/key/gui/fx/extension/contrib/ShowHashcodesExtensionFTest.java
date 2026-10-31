/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.pp.PosInSequent;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Toolkit-free tests of the FX port of the hashcodes extension ({@link ShowHashcodesExtensionF}):
 * the service-loaded provider declares its {@link KeYGuiExtensionF.Info} exactly like the Swing
 * original (ShowHashcodesExtension.java:20-24), is instantiable without a running FX toolkit,
 * implements the portable {@link KeYGuiExtensionF.TooltipF} capability, guards the null and
 * whole-sequent positions with the empty list (Swing ShowHashcodesExtension.java:29-31) and is
 * registered in the FX service-loader file. The tooltip content itself (operator hash, LHS
 * hash/sort of elementary updates) needs a real {@code PosInOccurrence} over a term, which
 * requires the proof machinery; the composed strings surface in the sequent-view hover tooltip
 * (SequentViewF#getTooltipText) and are covered by the in-app verification instead.
 */
class ShowHashcodesExtensionFTest {

    private final ShowHashcodesExtensionF extension = new ShowHashcodesExtensionF();

    @Test
    void infoAnnotationMirrorsTheSwingOriginal() {
        KeYGuiExtensionF.Info info =
            ShowHashcodesExtensionF.class.getAnnotation(KeYGuiExtensionF.Info.class);
        assertThat(info).isNotNull();
        assertThat(info.name()).isEqualTo("Show Hashcodes");
        assertThat(info.optional()).isTrue();
        assertThat(info.experimental()).isFalse();
        assertThat(info.description())
                .isEqualTo("GUI Extension for showing hash codes in tooltips");
    }

    @Test
    void providerIsInstantiableHeadlessAndImplementsTooltipF() {
        // the provider itself is constructible headless (no FX toolkit required, stateless)
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.TooltipF.class);
        assertThat(new ShowHashcodesExtensionF()).isNotSameAs(extension);
    }

    @Test
    void nullPositionYieldsNoStrings() {
        assertThat(extension.getTooltipStrings(null, null)).isEmpty();
    }

    @Test
    void wholeSequentPositionYieldsNoStrings() {
        assertThat(extension.getTooltipStrings(null, PosInSequent.createSequentPos())).isEmpty();
    }

    @Test
    void nullPosInOccurrenceYieldsNoStrings() {
        // defensive guard beyond the Swing original (which would NPE): the FX hover machinery
        // only passes positions with a sub term, SequentViewF.java:1692
        assertThat(extension.getTooltipStrings(new KeYMediatorF(), PosInSequent.createSequentPos()))
                .isEmpty();
    }

    @Test
    void serviceRegistrationNamesTheProvider() throws IOException {
        try (InputStream in = ShowHashcodesExtensionFTest.class.getClassLoader()
                .getResourceAsStream(
                    "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF")) {
            assertThat(in).as("service-loader file on the classpath").isNotNull();
            String content = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            assertThat(content)
                    .contains("de.uka.ilkd.key.gui.fx.extension.contrib.ShowHashcodesExtensionF");
        }
    }
}
