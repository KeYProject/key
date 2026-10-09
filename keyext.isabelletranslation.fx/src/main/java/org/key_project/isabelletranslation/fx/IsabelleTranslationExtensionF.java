/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.fx;

import java.util.List;
import javafx.scene.control.MenuItem;
import javafx.stage.Window;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The Isabelle translation extension, JavaFX port of
 * {@code org.key_project.isabelletranslation.IsabelleTranslationExtension} (Swing
 * IsabelleTranslationExtension.java:28-68): translates the sequent of a goal to an Isabelle theory
 * and checks the translation with the Isabelle backend.
 * <p>
 * The FX port implements the same three capability slots as the Swing original
 * (IsabelleTranslationExtension.java:30-31, {@code Settings}, {@code ContextMenu},
 * {@code Startup}): the Isabelle settings panel, the SEQUENT_VIEW context-menu entries
 * ("Translate to Isabelle" / "Translate all goals to Isabelle") and the startup hook that
 * initializes {@link IsabelleTranslationSettings}.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing actions ({@code IsabelleTranslationAction.solveGoals},
 * IsabelleTranslationAction.java:47-81) hand the generated theories to the external Isabelle
 * solver ({@code IsabelleLauncher}) and present a progress/model dialog. The FX port only runs
 * the sequent translation ({@code IsabelleTranslator.translateProblem}, shared with Swing) and
 * shows the resulting Isabelle theory in a plain dialog — the solver launch and its progress
 * window are omitted (the heavy Scala/Isabelle dependency of the backend is never loaded by this
 * provider).
 */
@NullMarked
@KeYGuiExtensionF.Info(name = "Isabelle Translation", optional = true, experimental = false,
    description = "Translate the sequent of the selected goal into an Isabelle theory. "
        + "KNOWN-SIMPLIFIED (FX): the generated theory is shown in a dialog; launching the "
        + "external Isabelle solver to check the translation is deferred.")
public class IsabelleTranslationExtensionF implements KeYGuiExtensionF,
        KeYGuiExtensionF.SettingsF, KeYGuiExtensionF.ContextMenuF, KeYGuiExtensionF.StartupF {

    private static final Logger LOGGER =
        LoggerFactory.getLogger(IsabelleTranslationExtensionF.class);

    /** the settings panel, created lazily on first {@link #getSettings()} call */
    private IsabelleSettingsProviderF settingsProvider;

    @Override
    public SettingsProviderF getSettings() {
        // extension: MP9.3 — Swing IsabelleTranslationExtension.java:33-35: getSettings() returns
        // the Isabelle settings panel; the host registers it into the SettingsManagerF registry
        // (Swing SettingsManager.registerProvider). The panel is created lazily (Swing creates a
        // fresh panel per call), so constructing the provider itself stays side-effect free.
        if (settingsProvider == null) {
            settingsProvider = new IsabelleSettingsProviderF();
        }
        return settingsProvider;
    }

    @Override
    public List<MenuItem> getSequentContextItems(@Nullable KeYMediatorF mediator,
            @Nullable Goal goal, @Nullable PosInSequent pos) {
        // extension: MP9.3 — Swing ContextMenuAdapter (IsabelleTranslationExtension.java:41-56):
        // for ContextMenuKind.SEQUENT_VIEW the extension contributes the two translate actions
        // exactly when the click was NOT on a term inside a formula (pos.getPosInOccurrence()
        // == null) and a goal is selected. The FX SPI hands the clicked goal directly; the null
        // guards keep the same behaviour without a mediator round trip.
        if (pos == null || pos.getPosInOccurrence() != null || goal == null || mediator == null) {
            return List.of();
        }
        MenuItem translateGoal = new MenuItem("Translate to Isabelle");
        translateGoal.setOnAction(
            e -> IsabelleTranslationRunnerF.translateGoal(goal, ownerWindow(translateGoal)));
        MenuItem translateAllGoals = new MenuItem("Translate all goals to Isabelle");
        translateAllGoals.setOnAction(
            e -> IsabelleTranslationRunnerF.translateAllGoals(goal,
                ownerWindow(translateAllGoals)));
        return List.of(translateGoal, translateAllGoals);
    }

    @Override
    public void init(MainWindowF window, KeYMediatorF mediator) {
        // extension: MP9.3 — Swing IsabelleTranslationExtension.java:65-67: the startup hook
        // initializes the settings singleton (loads the JSON settings file / installs the default
        // configuration and the shutdown-hook that saves it). IsabelleTranslationSettings itself
        // is plain Java (IsabelleTranslationSettings.java:25-223) but it lives in a module that
        // pulls key.ui (Swing) and the scala-isabelle backend transitively; the initialization is
        // kept defensive so a class-loading hiccup can never block the app startup.
        try {
            IsabelleTranslationSettings.getInstance();
        } catch (RuntimeException e) {
            LOGGER.error("Could not initialize the Isabelle translation settings", e);
        }
    }

    /**
     * The owner window of the context menu a menu item lives in, used as the dialog owner when
     * the translation result is shown; {@code null} when the popup is already gone (the dialog
     * then opens owner-less).
     *
     * @param item the clicked menu item
     * @return the owner window or {@code null}
     */
    private static @Nullable Window ownerWindow(MenuItem item) {
        var popup = item.getParentPopup();
        return popup != null ? popup.getOwnerWindow() : null;
    }
}
