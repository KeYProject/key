/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.profileloading;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.wd.WdProfile;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Toolkit-free tests of the FX port of the WD loading-options provider
 * ({@link WDLoadDialogOptionPanelF}): the provider declares its {@link KeYGuiExtensionF.Info}
 * exactly like the Swing original ({@code experimental = false}, no name — Swing parity,
 * WDLoadDialogOptionPanel.java:23-24), is instantiable without a running FX toolkit, implements
 * the portable {@link KeYGuiExtensionF.LoadOptionPanelF} capability with the WD profile
 * {@link WdProfile#INSTANCE} (Swing {@code getProfile}, WDLoadDialogOptionPanel.java:32-34) and
 * is registered in the FX service-loader file. {@link WDLoadDialogOptionPanelF#get()} is
 * deliberately not called here: it constructs the {@link WDLoadOptionPanelF} panel, which builds
 * FX controls in its constructor and therefore requires a running JavaFX toolkit — the panel
 * content (radio group, {@code getResult()} mapping to {@code wdOperator:<L|Y|D>}) is covered by
 * the in-app verification ({@code key.fx.verify.profileloading}) instead.
 */
class WDLoadDialogOptionPanelFTest {

    private final WDLoadDialogOptionPanelF provider = new WDLoadDialogOptionPanelF();

    @Test
    void infoAnnotationMirrorsTheSwingOriginal() {
        KeYGuiExtensionF.Info info =
            WDLoadDialogOptionPanelF.class.getAnnotation(KeYGuiExtensionF.Info.class);
        assertThat(info).isNotNull();
        // Swing parity (WDLoadDialogOptionPanel.java:23-24): experimental = false, no name
        assertThat(info.experimental()).isFalse();
        assertThat(info.name()).isEmpty();
    }

    @Test
    void providerIsInstantiableHeadlessAndImplementsLoadOptionPanelF() {
        // the provider itself is constructible headless (no FX toolkit required); the panel
        // construction is lazy in get() and stays untested here (FX controls)
        assertThat(provider).isInstanceOf(KeYGuiExtensionF.class);
        assertThat(provider).isInstanceOf(KeYGuiExtensionF.LoadOptionPanelF.class);
    }

    @Test
    void profileIsTheWdProfile() {
        Profile profile = provider.getProfile();
        assertThat(profile).isSameAs(WdProfile.INSTANCE);
        assertThat(profile.displayName()).isEqualTo("Java Profile + Well-Definedness Checks");
    }

    @Test
    void serviceRegistrationNamesTheProvider() throws IOException {
        try (InputStream in = WDLoadDialogOptionPanelFTest.class.getClassLoader()
                .getResourceAsStream(
                    "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF")) {
            assertThat(in).as("service-loader file on the classpath").isNotNull();
            String content = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            assertThat(content)
                    .contains("de.uka.ilkd.key.gui.fx.profileloading.WDLoadDialogOptionPanelF");
        }
    }
}
