/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.originlabels;

import java.util.ArrayList;
import java.util.List;
import javafx.scene.control.Alert;
import javafx.scene.control.ButtonType;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.actions.QuickSaveF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentViewF;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.TermLabelSettings;

import org.key_project.logic.Name;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * JavaFX port of the origin-tracking / term-label view controls. The Swing original consists of
 * <ul>
 * <li>{@code de.uka.ilkd.key.gui.actions.TermLabelMenu} (View menu "Term Labels") — ported as
 * {@link TermLabelMenuF},</li>
 * <li>{@code de.uka.ilkd.key.gui.actions.HidePackagePrefixToggleAction} (View menu "Hide Package
 * Prefix"),</li>
 * <li>the "Origin Tracking" main-menu contributions of
 * {@code de.uka.ilkd.key.gui.originlabels.OriginTermLabelsExt} (the extension's MainMenu kind):
 * "Toggle Term Origin Tracking" and "Show origin" (the latter arrives with the
 * {@code OriginTermLabelVisualizerF} window, see the originlabels package).</li>
 * </ul>
 * This class assembles the corresponding items for the FX View menu ({@link #install}) and
 * provides the development self test ({@link #verify}, {@code key.fx.verify.lemmaorigin}).
 * <p>
 * Deviations from Swing:
 * <ul>
 * <li>The FX sequent view has no term context menu yet, so "Show Origin" is a View menu item
 * instead of a context-menu action (Swing {@code ShowOriginAction} is a context-menu
 * contribution).</li>
 * <li>"Toggle Term Origin Tracking" reloads via quick save + quick load
 * ({@code QuickSaveF}, the FX counterpart of Swing {@code QuickSaveAction/QuickLoadAction} used
 * by Swing's {@code ToggleTermOriginTrackingAction}). The setting is flipped <em>before</em> the
 * reload so the re-created proof actually carries the new labels (in Swing the flip happens
 * after the reload, which cannot affect the reloaded proof).</li>
 * <li>The "Highlight Origins" toggle is not ported: it gates the sequent→source-view origin
 * highlight ({@code SequentViewInputListener.highlightOriginInSourceView}), which has no FX
 * counterpart yet (SourceViewF lacks the highlight API).</li>
 * </ul>
 */
public final class OriginLabelsF {

    private static final Logger LOGGER = LoggerFactory.getLogger(OriginLabelsF.class);

    /** the installed term labels submenu (for the self test), set by {@link #install}. */
    private static TermLabelMenuF termLabelMenu;

    private OriginLabelsF() {
    }

    /**
     * Builds the View-menu items (Swing View menu "Term Labels" + "Hide Package Prefix" + the
     * "Origin Tracking" extension menu): the term labels submenu, the package-prefix toggle and
     * the origin-tracking submenu. Also installs the term label visibility into the sequent view
     * and observes the selection to rebuild the label items per proof.
     *
     * @param mainWindow the FX main window
     * @return the items to append to the View menu
     */
    public static List<MenuItem> install(MainWindowF mainWindow) {
        SequentViewF sequentView = mainWindow.getSequentView();

        // the sequent view prints through the shared visibility manager (Swing:
        // SequentView printer uses mainWindow.getVisibleTermLabels()); a reprint is needed on
        // every visibility change (Swing MainWindow.makePrettyView)
        termLabelMenu =
            new TermLabelMenuF(() -> mainWindow.getSequentView().printSequent());
        sequentView.setVisibleTermLabels(termLabelMenu.getVisibleTermLabels());

        // Swing TermLabelMenu rebuilds on selectedProofChanged (label names depend on the proof)
        KeYSelectionModel selectionModel = mainWindow.getSelectionModel();
        selectionModel.addKeYSelectionListenerChecked(new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
                termLabelMenu.rebuildMenu(selectionModel.getSelectedProof());
            }
        });
        termLabelMenu.rebuildMenu(selectionModel.getSelectedProof());

        List<MenuItem> items = new ArrayList<>();
        items.add(termLabelMenu);
        items.add(createHidePackagePrefixItem(mainWindow));
        items.add(new SeparatorMenuItem());
        items.add(createOriginTrackingMenu(mainWindow));
        return items;
    }

    /**
     * The "Hide Package Prefix" toggle (Swing {@code HidePackagePrefixToggleAction}): flips
     * {@code NotationInfo.DEFAULT_HIDE_PACKAGE_PREFIX} (before the setting, like Swing, because
     * the printer construction reads the static) and the ViewSettings value, then re-prints.
     */
    private static MenuItem createHidePackagePrefixItem(MainWindowF mainWindow) {
        CheckMenuItem item = new CheckMenuItem("Hide Package Prefix");
        boolean hide = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .isHidePackagePrefix();
        NotationInfo.DEFAULT_HIDE_PACKAGE_PREFIX = hide;
        item.setSelected(hide);
        item.setOnAction(e -> {
            boolean selected = item.isSelected();
            // must be executed before the ViewSettings are modified, like the Swing original
            NotationInfo.DEFAULT_HIDE_PACKAGE_PREFIX = selected;
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .setHidePackagePrefix(selected);
            mainWindow.getSequentView().printSequent();
        });
        return item;
    }

    /**
     * The "Origin Tracking" submenu (Swing {@code OriginTermLabelsExt.getMainMenuActions}):
     * "Toggle Term Origin Tracking" with the Swing reload dialog, plus "Show Origin" once the
     * {@link OriginTermLabelVisualizerF} is available.
     */
    private static MenuItem createOriginTrackingMenu(MainWindowF mainWindow) {
        Menu menu = new Menu("Origin Tracking");

        CheckMenuItem tracking = new CheckMenuItem("Toggle Term Origin Tracking");
        tracking.setSelected(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
        tracking.setOnAction(e -> toggleTermOriginTracking(mainWindow, tracking));
        menu.getItems().add(tracking);
        return menu;
    }

    /**
     * The Swing {@code ToggleTermOriginTrackingAction.actionPerformed}: confirm dialog
     * ("For the change to take effect, you need to reload the proof."), then flip
     * {@code TermLabelSettings.useOriginLabels} and optionally reload (quick save + quick load).
     */
    private static void toggleTermOriginTracking(MainWindowF mainWindow,
            CheckMenuItem tracking) {
        TermLabelSettings settings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings();

        Alert alert = new Alert(Alert.AlertType.CONFIRMATION);
        alert.setTitle("Origin");
        alert.setHeaderText(null);
        alert.setContentText("For the change to take effect, you need to reload the proof.");
        ButtonType reload = new ButtonType("Reload");
        ButtonType cont = new ButtonType("Continue without reloading");
        alert.getButtonTypes().setAll(reload, cont, ButtonType.CANCEL);
        alert.initOwner(mainWindow.getStage());
        ButtonType choice = alert.showAndWait().orElse(ButtonType.CANCEL);
        if (choice == ButtonType.CANCEL) {
            tracking.setSelected(settings.getUseOriginLabels());
            return;
        }
        boolean newValue = !settings.getUseOriginLabels();
        settings.setUseOriginLabels(newValue);
        if (choice == reload) {
            // Swing quick-saves and quick-loads; the FX quick save stores the current proof
            // state, the quick load re-creates it (with the new label setting applied)
            QuickSaveF.quickSave(mainWindow);
            QuickSaveF.quickLoad(mainWindow);
        }
        tracking.setSelected(newValue);
    }

    // ------------------------------------------------------------------
    // self test (key.fx.verify.lemmaorigin)
    // ------------------------------------------------------------------

    /**
     * Development self test: verifies that term labels can be shown/hidden in the sequent view
     * through the shared visibility manager (Swing View▸Term Labels). The report is a single
     * line ending in {@code PASS} or {@code FAIL}.
     *
     * @param mainWindow the FX main window with a loaded proof
     * @return the report line
     */
    public static String verify(MainWindowF mainWindow) {
        SequentViewF view = mainWindow.getSequentView();
        if (termLabelMenu == null || view.getProof() == null) {
            return "termLabels: no proof FAIL";
        }
        de.uka.ilkd.key.control.TermLabelVisibilityManager manager =
            termLabelMenu.getVisibleTermLabels();
        List<Name> names = TermLabelVisibilityManager.getSortedTermLabelNames(view.getProof());
        String before = view.printedText();
        // show every label (Swing default state of the TermLabelVisibilityManager)
        for (Name name : names) {
            manager.setHidden(name, false);
        }
        manager.setShowLabels(true);
        String shown = view.printedText();
        boolean grew = shown.length() > before.length();
        // find a label whose printed name is part of the rendered text
        Name printed = names.stream()
                .filter(n -> shown.contains(n.toString())).findFirst().orElse(null);
        boolean hiddenOk = true;
        if (printed != null) {
            manager.setHidden(printed, true);
            String hidden = view.printedText();
            hiddenOk = !hidden.contains(printed.toString());
            manager.setHidden(printed, false);
        }
        // restore the pre-test state: show all labels (the default of the manager)
        manager.setShowLabels(true);
        LOGGER.info("verify term labels: names={} grew={} printedLabel={} hiddenOk={}",
            names.size(),
            grew, printed, hiddenOk);
        boolean pass = grew && printed != null && hiddenOk;
        return "termLabels: names=" + names.size() + " chars " + before.length() + "->"
            + shown.length() + " printedLabel=" + printed + " " + (pass ? "PASS" : "FAIL");
    }
}
