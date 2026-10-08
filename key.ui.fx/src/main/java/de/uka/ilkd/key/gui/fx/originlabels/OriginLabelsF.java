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
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.nodeinfo.NodeInfoVisualizerF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentViewF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.TermLabelSettings;

import org.key_project.logic.Name;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;

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
     * "Toggle Term Origin Tracking" with the Swing reload dialog and "Show Origin", which opens
     * the {@link OriginTermLabelVisualizerF} window for the last clicked term (in Swing the
     * action is a sequent context-menu contribution; the FX sequent view has no context menu
     * yet, so the item lives here).
     */
    private static MenuItem createOriginTrackingMenu(MainWindowF mainWindow) {
        Menu menu = new Menu("Origin Tracking");

        CheckMenuItem tracking = new CheckMenuItem("Toggle Term Origin Tracking");
        tracking.setSelected(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
        tracking.setOnAction(e -> toggleTermOriginTracking(mainWindow, tracking));
        menu.getItems().add(tracking);

        MenuItem showOrigin =
            menuItem("Show Origin", mainWindow, IconFactoryF.Key.INFO_VIEW,
                () -> showOrigin(mainWindow));
        menu.getItems().add(showOrigin);
        return menu;
    }

    /** Helper building a plain menu item (JavaFX MenuItem has no tooltip API). */
    private static MenuItem menuItem(String text, MainWindowF mainWindow, IconFactoryF.Key icon,
            Runnable action) {
        javafx.scene.control.MenuItem item = new javafx.scene.control.MenuItem(text);
        if (icon != null) {
            item.setGraphic(IconFactoryF.createIcon(icon));
        }
        item.setOnAction(e -> action.run());
        return item;
    }

    /**
     * The Swing {@code ShowOriginAction.actionPerformed}: opens a new origin visualizer for the
     * selected term. The position is the last clicked term of the sequent view, walked up to a
     * formula ({@code TermView} can only print sequents or formulas, not terms); with no term
     * clicked the whole sequent is shown. Enablement follows
     * {@code TermLabelSettings.useOriginLabels}.
     */
    private static void showOrigin(MainWindowF mainWindow) {
        boolean enabled =
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels();
        if (!enabled) {
            NotificationManagerF.getInstance().notify(
                "Origin tracking is switched off (View▸Origin Tracking▸Toggle Term Origin Tracking).",
                Kind.WARNING);
            return;
        }
        de.uka.ilkd.key.gui.fx.nodeviews.SequentViewF view = mainWindow.getSequentView();
        de.uka.ilkd.key.pp.PosInSequent pos = view.getLastClickedPos();
        PosInOccurrence pio = pos == null ? null : pos.getPosInOccurrence();
        // OriginTermLabelVisualizer.TermView can only print sequents or formulas, not terms
        while (pio != null && !pio.subTerm().sort().equals(JavaDLTheory.FORMULA)) {
            pio = pio.up();
        }
        Node node = mainWindow.getSelectionModel().getSelectedNode();
        if (node == null) {
            NotificationManagerF.getInstance().notify("No proof node selected.", Kind.WARNING);
            return;
        }
        OriginTermLabelVisualizerF visualizer =
            new OriginTermLabelVisualizerF(mainWindow, pio, node,
                mainWindow.getSelectionModel().getSelectedProof().getServices());
        visualizer.show();
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
     * through the shared visibility manager (Swing View▸Term Labels) and that the origin
     * visualizer window registers/disposes and builds its tree for the loaded proof. The report
     * is a single line ending in {@code PASS} or containing {@code FAIL}.
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
        String termLabelReport = "termLabels: names=" + names.size() + " chars " + before.length()
            + "->" + shown.length() + " printedLabel=" + printed + " " + (pass ? "PASS" : "FAIL");

        // --- origin visualizer part (Swing OriginTermLabelVisualizer / NodeInfoVisualizer) ---
        String visReport = verifyOriginVisualizer(mainWindow);
        return termLabelReport + " | " + visReport;
    }

    /**
     * Self test part 2 (Swing {@code OriginTermLabelVisualizer}): opens the visualizer for the
     * first sequent formula of the selected node, verifies that it registered itself
     * ({@link NodeInfoVisualizerF} registry), that its origin tree has rows and that the term
     * view printed something, then disposes it and verifies that the registry is empty again.
     */
    private static String verifyOriginVisualizer(MainWindowF mainWindow) {
        Node node = mainWindow.getSelectionModel().getSelectedNode();
        if (node == null) {
            return "originVis: no node FAIL";
        }
        // first top-level formula of the sequent (Swing ShowOriginAction walks up to a formula;
        // the first formula is as good a demonstration position as any)
        PosInOccurrence pio = null;
        for (SequentFormula cfma : node.sequent().antecedent()) {
            pio = new PosInOccurrence(cfma, org.key_project.logic.PosInTerm.getTopLevel(), true);
            break;
        }
        if (pio == null) {
            for (SequentFormula cfma : node.sequent().succedent()) {
                pio = new PosInOccurrence(cfma, org.key_project.logic.PosInTerm.getTopLevel(),
                    false);
                break;
            }
        }
        if (pio == null) {
            return "originVis: empty sequent FAIL";
        }
        try {
            OriginTermLabelVisualizerF visualizer =
                new OriginTermLabelVisualizerF(mainWindow, pio, node, node.proof().getServices());
            visualizer.show();
            boolean registered = NodeInfoVisualizerF.hasInstances(node);
            int rows = visualizer.treeRowCount();
            boolean viewPrinted = visualizer.viewPrinted();
            visualizer.dispose();
            boolean unregistered = !NodeInfoVisualizerF.hasInstances(node);
            LOGGER.info("verify origin visualizer: registered={} rows={} viewPrinted={} "
                + "unregistered={}", registered, rows, viewPrinted, unregistered);
            boolean pass = registered && rows > 1 && viewPrinted && unregistered;
            return "originVis: rows=" + rows + " " + (pass ? "PASS" : "FAIL");
        } catch (RuntimeException e) {
            LOGGER.warn("verify origin visualizer failed", e);
            return "originVis: exception " + e + " FAIL";
        }
    }
}
