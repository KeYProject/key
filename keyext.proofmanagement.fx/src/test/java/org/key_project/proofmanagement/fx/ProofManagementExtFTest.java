/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.proofmanagement.fx;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.List;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless unit tests of the proof management FX extension (MP9.6):
 * <ul>
 * <li>the {@link KeYGuiExtensionF.Info} annotation mirrors the Swing original
 * ({@code ProofManagementExt}: name "Proof management", optional, non-experimental),</li>
 * <li>the provider contributes the "Proof Management" menu with the single active action
 * "Check proof bundle ..." (the Merge/Bundle actions are commented out in the Swing original and
 * are not ported),</li>
 * <li>the service-loader registration file lists the provider — the wiring that makes the
 * extension reach the runtime discovery of {@code key.ui.fx} (the file-based assertion avoids
 * constructing the sibling providers, whose settings panels require a running FX toolkit and
 * would fail in a headless unit test).</li>
 * </ul>
 */
class ProofManagementExtFTest {

    /** The service-loader resource registered by this module. */
    private static final String SERVICE_FILE =
        "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF";

    @Test
    void declaresInfoAnnotation() {
        KeYGuiExtensionF.Info info =
            ProofManagementExtF.class.getAnnotation(KeYGuiExtensionF.Info.class);
        assertNotNull(info, "the provider must carry the @Info annotation");
        assertEquals("Proof management", info.name());
        assertTrue(info.optional(), "mirrors the optional flag of the Swing original");
        assertFalse(info.experimental(), "non-experimental like the Swing original");
    }

    @Test
    void contributesProofManagementMenu() {
        Menu menu = ProofManagementExtF.buildMenu(null);
        assertEquals("Proof Management", menu.getText());
        List<MenuItem> items = menu.getItems();
        assertEquals(1, items.size(), "only the active CheckAction is ported");
        MenuItem check = items.get(0);
        assertEquals("Check proof bundle ...", check.getText());
        assertNotNull(check.getOnAction(), "the item must open the check dialog on action");
    }

    @Test
    void registersViaServiceLoaderFile() throws Exception {
        List<String> providers;
        try (InputStream in =
            ProofManagementExtF.class.getClassLoader().getResourceAsStream(SERVICE_FILE)) {
            assertNotNull(in, "the service-loader file must be on the classpath");
            providers = new BufferedReader(new InputStreamReader(in, StandardCharsets.UTF_8))
                    .lines()
                    .map(String::trim)
                    .filter(l -> !l.isEmpty() && !l.startsWith("#"))
                    .toList();
        }
        assertEquals(List.of(ProofManagementExtF.class.getName()), providers,
            "the service-loader file must list exactly the provider FQCN");
    }
}
