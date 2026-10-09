/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.fx;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import javafx.application.Platform;
import javafx.scene.control.MenuItem;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless unit test of the MP9.3 FX port of the Isabelle translation extension
 * ({@link IsabelleTranslationExtensionF}): the {@link KeYGuiExtensionF.Info} metadata, the
 * settings contribution and the sequent context-menu contribution (including the null guards of
 * the SPI call).
 * <p>
 * Like the other extension tests of this repository the term-level assertion runs against a real
 * {@link Goal} of a headlessly loaded trivial proof ({@code \problem { true }}, same pattern as
 * {@code SequentMenuModelFTest}). Constructing JavaFX controls (the settings panel, the menu
 * items) requires the JavaFX toolkit, which is started once in {@link #initFx()} (no window is
 * ever shown; the toolkit runs with software rendering).
 */
class IsabelleTranslationExtensionFTest {

    private KeYEnvironment<DefaultUserInterfaceControl> env;

    @BeforeAll
    static void initFx() {
        try {
            Platform.startup(() -> {
            });
        } catch (IllegalStateException e) {
            // the platform is already running (e.g. a shared test JVM)
        }
        // keep the toolkit alive without any open window for the whole test class
        Platform.setImplicitExit(false);
    }

    @AfterEach
    void tearDown() {
        if (env != null) {
            env.dispose();
            env = null;
        }
    }

    @Test
    void infoAnnotationDeclaresTheExtension() {
        KeYGuiExtensionF.Info info = new IsabelleTranslationExtensionF().getClass()
                .getAnnotation(KeYGuiExtensionF.Info.class);
        assertNotNull(info, "@Info must be present on the provider");
        assertEquals("Isabelle Translation", info.name());
        assertTrue(info.optional(), "the Swing original is optional (the user may disable it)");
        assertFalse(info.experimental(),
            "the Swing original is not experimental (IsabelleTranslationExtension.java:29)");
    }

    @Test
    void settingsContribution() {
        IsabelleTranslationExtensionF extension = new IsabelleTranslationExtensionF();
        SettingsProviderF settings = extension.getSettings();
        assertNotNull(settings, "the extension must contribute a settings provider");
        assertTrue(settings instanceof IsabelleSettingsProviderF,
            "the provider must be the FX settings panel");
        assertEquals("Isabelle Translation", settings.getDescription());
    }

    @Test
    void contextMenuGuardsNullInputs() {
        IsabelleTranslationExtensionF extension = new IsabelleTranslationExtensionF();
        // null inputs must never crash (the SPI call is guarded by the provider itself)
        assertEquals(List.of(), extension.getSequentContextItems(null, null, null));
    }

    @Test
    void contextMenuProducesTranslateItemsForSequentPosition() throws Exception {
        KeYMediatorF mediator = mediatorWithGoal();
        Goal goal = mediator.getSelectedGoal();
        assertNotNull(goal, "the demo problem must produce a selectable goal");

        IsabelleTranslationExtensionF extension = new IsabelleTranslationExtensionF();
        // Swing parity (IsabelleTranslationExtension.java:48): the two translate actions appear
        // for a sequent-level click (PosInSequent without an occurrence) on a selected goal.
        List<MenuItem> items =
            extension.getSequentContextItems(mediator, goal, PosInSequent.createSequentPos());
        assertEquals(2, items.size(), "both translate actions must be contributed");
        assertEquals("Translate to Isabelle", items.get(0).getText());
        assertEquals("Translate all goals to Isabelle", items.get(1).getText());
        assertNotNull(items.get(0).getOnAction(), "the single-goal action must be wired");
        assertNotNull(items.get(1).getOnAction(), "the all-goals action must be wired");
    }

    /**
     * Loads {@code \problem { true }} headlessly and selects the root goal in a fresh mediator.
     */
    private KeYMediatorF mediatorWithGoal() throws Exception {
        Path dir = Files.createTempDirectory("isabelletranslation-fx");
        Path main = dir.resolve("test.key");
        // No \include: the JavaDL profile loads the standard library from the classpath.
        Files.writeString(main, "\\problem { true }\n");
        env = KeYEnvironment.load(main);
        KeYMediatorF mediator = new KeYMediatorF();
        mediator.getSelectionModel().setSelectedProof(env.getLoadedProof());
        assertNotNull(mediator.getSelectedGoal(), "the root goal must be selectable");
        return mediator;
    }
}
