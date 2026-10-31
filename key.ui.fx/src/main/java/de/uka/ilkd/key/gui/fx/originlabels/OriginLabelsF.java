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
import de.uka.ilkd.key.gui.fx.nodeinfo.NodeInfoVisualizerF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentViewF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
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
 * <li>the "Origin Tracking" main-menu contribution of
 * {@code de.uka.ilkd.key.gui.originlabels.OriginTermLabelsExt} (the extension's MainMenu kind):
 * "Toggle Term Origin Tracking" (the Swing "Highlight Origins" second toggle is not ported,
 * see the deviations below).</li>
 * </ul>
 * This class assembles the corresponding items ({@link #install} — the legacy direct wiring of
 * the FX View menu, {@code MainWindowF#buildViewMenu} line 4275 — and {@link #extensionMenus},
 * the SPI-servable variant served by the provider {@code OriginTermLabelsExtF}) and provides the
 * development self test ({@link #verify}, {@code key.fx.verify.lemmaorigin}).
 * <p>
 * The cluster is served through the extension SPI now: {@code OriginTermLabelsExtF}
 * (MainMenuF, {@code getMenuPath() == "View"}) contributes the menus built here, so the
 * host's direct {@code OriginLabelsF.install(this)} call is superseded and will be removed by
 * the host edit. Both entry points share the single-shot installation {@link #installOnce}.
 * <p>
 * Deviations from Swing:
 * <ul>
 * <li>"Show Origin" is a sequent context-menu contribution again (Swing parity, the Swing
 * {@code ShowOriginAction} is a SEQUENT_VIEW context action served by
 * {@code OriginTermLabelsExtF.ContextMenuF}); the View-menu placement of this port was the
 * stopgap for the then-missing FX sequent context menu and is resolved.</li>
 * <li>"Toggle Term Origin Tracking" reloads via quick save + quick load
 * ({@code QuickSaveF}, the FX counterpart of Swing {@code QuickSaveAction/QuickLoadAction} used
 * by Swing's {@code ToggleTermOriginTrackingAction}). The setting is flipped <em>before</em> the
 * reload so the re-created proof actually carries the new labels (in Swing the flip happens
 * after the reload, which cannot affect the reloaded proof).</li>
 * <li>The "Highlight Origins" toggle is not ported: it gates the sequent→source-view origin
 * highlight ({@code SequentViewInputListener.highlightOriginInSourceView}), which has no FX
 * counterpart yet (SourceViewF lacks the highlight API).</li>
 * <li>KNOWN-SIMPLIFIED: the installation is single-shot ({@link #installOnce}) — the first
 * caller (the legacy View-menu wiring coexisting with the SPI provider until the host edit,
 * then the provider alone) builds the items and wires the sequent view; repeated calls return
 * an empty list, so menu-bar rebuilds (the verify harness) do not duplicate the cluster.</li>
 * </ul>
 */
public final class OriginLabelsF {

    private static final Logger LOGGER = LoggerFactory.getLogger(OriginLabelsF.class);

    /**
     * the single-shot installation guard of {@link #installOnce}: the menu items and the
     * sequent-view/selection wiring are created exactly once, shared by {@link #install} (the
     * legacy direct View-menu wiring) and {@link #extensionMenus} (the SPI-served variant);
     * whichever runs first wins, repeated calls return an empty list.
     */
    private static boolean installed;

    /** the installed term labels submenu (for the self test), set by {@link #installOnce}. */
    private static TermLabelMenuF termLabelMenu;

    /** the installed "Hide Package Prefix" check item, set by {@link #installOnce}. */
    private static CheckMenuItem hidePackagePrefixItem;

    /** the installed "Origin Tracking" submenu, set by {@link #installOnce}. */
    private static Menu originTrackingMenu;

    private OriginLabelsF() {
    }

    /**
     * Builds the View-menu items (Swing View menu "Term Labels" + "Hide Package Prefix" + the
     * "Origin Tracking" extension menu): the term labels submenu, the package-prefix toggle and
     * the origin-tracking submenu. Also installs the term label visibility into the sequent view
     * and observes the selection to rebuild the label items per proof.
     * <p>
     * This is the legacy direct wiring ({@code MainWindowF#buildViewMenu} line 4275); the
     * SPI provider {@code OriginTermLabelsExtF} serves the same cluster through
     * {@link #extensionMenus}, so this call is superseded and will be removed by the host edit.
     *
     * @param mainWindow the FX main window
     * @return the items to append to the View menu; empty when this class already installed its
     *         cluster (single-shot {@link #installOnce})
     */
    public static List<MenuItem> install(MainWindowF mainWindow) {
        if (!installOnce(mainWindow)) {
            return List.of();
        }
        List<MenuItem> items = new ArrayList<>();
        items.add(termLabelMenu);
        items.add(hidePackagePrefixItem);
        items.add(new SeparatorMenuItem());
        items.add(originTrackingMenu);
        return items;
    }

    /**
     * The SPI-servable variant of {@link #install} for {@code OriginTermLabelsExtF.MainMenuF}:
     * the same cluster shaped as {@link Menu} objects — the facade splices the contributed
     * menus into the built-in View menu matched by the provider's {@code getMenuPath()}.
     * Deviations from the flat {@link #install} shape (the JavaFX SPI contributes whole menus
     * only):
     * <ul>
     * <li>KNOWN-SIMPLIFIED: the flat "Hide Package Prefix" check item becomes a single-item
     * submenu of the same name — a JavaFX {@link CheckMenuItem} cannot be contributed through
     * the menu-only MainMenuF surface.</li>
     * <li>KNOWN-SIMPLIFIED: the flat separator of the View-menu cluster is dropped (the
     * contributed menus are visually separated as menus), and the cluster lands at the end of
     * the View menu instead of right after "Syntax Highlighting" (the facade appends provider
     * menus after the built-in items; the MP3a Swing order applies to the legacy wiring).</li>
     * </ul>
     *
     * @param mainWindow the FX main window
     * @return the menus to contribute under the View menu; empty when this class already
     *         installed its cluster (single-shot {@link #installOnce})
     */
    public static List<Menu> extensionMenus(MainWindowF mainWindow) {
        if (!installOnce(mainWindow)) {
            return List.of();
        }
        Menu hidePackagePrefixMenu = new Menu("Hide Package Prefix");
        hidePackagePrefixMenu.getItems().add(hidePackagePrefixItem);
        return List.of(termLabelMenu, hidePackagePrefixMenu, originTrackingMenu);
    }

    /**
     * The shared single-shot installation: the term label visibility wiring (sequent view +
     * selection listeners) and the three cluster items. Only the first caller performs it;
     * later callers get {@code false} and contribute nothing.
     *
     * @return {@code true} if this call performed the installation
     */
    private static boolean installOnce(MainWindowF mainWindow) {
        if (installed) {
            return false;
        }
        installed = true;

        SequentViewF sequentView = mainWindow.getSequentView();

        // the sequent view prints through the shared visibility manager (Swing:
        // SequentView printer uses mainWindow.getVisibleTermLabels()); a reprint is needed on
        // every visibility change (Swing MainWindow.makePrettyView)
        termLabelMenu =
            new TermLabelMenuF(() -> mainWindow.getSequentView().printSequent());
        sequentView.setVisibleTermLabels(termLabelMenu.getVisibleTermLabels());

        // Swing TermLabelMenu rebuilds on selectedProofChanged (label names depend on the proof)
        // and re-styles the label items on selectedNodeChanged (bold = occurs in the displayed
        // sequent, B17)
        KeYSelectionModel selectionModel = mainWindow.getSelectionModel();
        selectionModel.addKeYSelectionListenerChecked(new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
                termLabelMenu.rebuildMenu(selectionModel.getSelectedProof());
                termLabelMenu.applyStyles(selectionModel.getSelectedNode());
            }

            @Override
            public void selectedNodeChanged(KeYSelectionEvent<Node> event) {
                // P3b/B17: Swing TermLabelMenu.selectedNodeChanged — the font style indicates
                // whether a label occurs in the currently displayed sequent
                termLabelMenu.applyStyles(selectionModel.getSelectedNode());
            }
        });
        termLabelMenu.rebuildMenu(selectionModel.getSelectedProof());
        termLabelMenu.applyStyles(selectionModel.getSelectedNode());

        hidePackagePrefixItem = createHidePackagePrefixItem(mainWindow);
        originTrackingMenu = createOriginTrackingMenu(mainWindow);
        return true;
    }

    /**
     * The "Hide Package Prefix" toggle (Swing {@code HidePackagePrefixToggleAction}): flips
     * {@code NotationInfo.DEFAULT_HIDE_PACKAGE_PREFIX} (before the setting, like Swing, because
     * the printer construction reads the static) and the ViewSettings value, then re-prints.
     */
    private static CheckMenuItem createHidePackagePrefixItem(MainWindowF mainWindow) {
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
     * The "Origin Tracking" submenu (Swing {@code OriginTermLabelsExt.getMainMenuActions},
     * OriginTermLabelsExt.java:63-69): "Toggle Term Origin Tracking" with the Swing reload
     * dialog. Swing's second MainMenu action "Highlight Origins" is not ported (see the class
     * javadoc); "Show Origin" is a Swing sequent context-menu contribution (ShowOriginAction,
     * SEQUENT_VIEW kind) and is served by {@code OriginTermLabelsExtF.ContextMenuF} — the
     * View-menu item of this port was the stopgap for the then-missing FX sequent context menu
     * and is resolved.
     */
    private static Menu createOriginTrackingMenu(MainWindowF mainWindow) {
        Menu menu = new Menu("Origin Tracking");

        CheckMenuItem tracking = new CheckMenuItem("Toggle Term Origin Tracking");
        tracking.setSelected(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
        tracking.setOnAction(e -> toggleTermOriginTracking(mainWindow, tracking));
        menu.getItems().add(tracking);
        return menu;
    }

    /**
     * The Swing {@code ShowOriginAction.actionPerformed} (ShowOriginAction.java:50-73): opens a
     * new origin visualizer for the given (clicked) term. The position is walked up to a
     * formula ({@code TermView} can only print sequents or formulas, not terms); with no term
     * clicked the whole sequent is shown. Enablement follows
     * {@code TermLabelSettings.useOriginLabels} — Swing disables the action for it
     * (ShowOriginAction.java:43-44, mirrored by the provider's context item); the guard stays
     * as the defensive path of the former View-menu stopgap.
     *
     * @param mainWindow the FX main window
     * @param pos the clicked position ({@code null} shows the whole sequent, like the Swing
     *        action's {@code PosInSequent.createSequentPos()} normalization)
     */
    static void showOrigin(MainWindowF mainWindow, PosInSequent pos) {
        boolean enabled =
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels();
        if (!enabled) {
            NotificationManagerF.getInstance().notify(
                "Origin tracking is switched off (View▸Origin Tracking▸Toggle Term Origin Tracking).",
                Kind.WARNING);
            return;
        }
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
        manager.setShowLabels(true);
        // walk the proof tree for a node whose printed sequent contains a term label (the root
        // sequent of the loaded problem usually has none — labels appear during the proof, so
        // the visibility test needs a node whose terms carry labels, like the user's view does)
        Proof proof = view.getProof();
        Name printed = null;
        Node labelNode = null;
        String shown = null;
        outer: for (Node node = proof.root(); node != null;) {
            mainWindow.getSelectionModel().setSelectedNode(node);
            String text = view.printedText();
            for (Name name : names) {
                if (text.contains(name.toString())) {
                    printed = name;
                    labelNode = node;
                    shown = text;
                    break outer;
                }
            }
            node = nextPreorderNode(node);
        }
        boolean grew = false, hiddenOk = true;
        if (printed != null) {
            // hide everything (Swing "Display Term Labels in Formulas" off) and back on
            manager.setShowLabels(false);
            String hidden = view.printedText();
            manager.setShowLabels(true);
            String shownAgain = view.printedText();
            grew = shownAgain.length() > hidden.length();
            hiddenOk = !hidden.contains(printed.toString()) && shown.contains(printed.toString());
        }
        // restore the default state: show all labels and select the root again
        manager.setShowLabels(true);
        mainWindow.getSelectionModel().setSelectedNode(proof.root());
        LOGGER.info("verify term labels: names={} printedLabel={} node={} grew={} hiddenOk={}",
            names.size(), printed, labelNode == null ? -1 : labelNode.serialNr(), grew, hiddenOk);
        boolean pass = printed != null && grew && hiddenOk;
        String termLabelReport = "termLabels: names=" + names.size() + " printedLabel=" + printed
            + (labelNode == null ? "" : " node=" + labelNode.serialNr()) + " "
            + (pass ? "PASS" : "FAIL");

        // --- origin visualizer part (Swing OriginTermLabelVisualizer / NodeInfoVisualizer) ---
        String visReport = verifyOriginVisualizer(mainWindow);

        // --- B17 persistence part: the Swing AbstractButtonSaver preference round trip ---
        String prefReport = verifyPreferencePersistence(proof);
        return termLabelReport + " | " + visReport + " | " + prefReport;
    }

    /**
     * Self test part (B17): the check states persist under the exact Swing
     * {@code AbstractButtonSaver} keys ("{@code <SimpleName>.<name>.selected}" in {@code
     * Preferences.userNodeForPackage(MainWindowF)}, PreferenceSaver.java:260) — driving the
     * user-click path must flip the menu state AND the raw preference, and reading the key back
     * must round-trip. One label name of the loaded proof is used when one exists; the toggled
     * states are restored afterwards (menu + preferences).
     *
     * @param proof the loaded proof (its term label names select the tested label item)
     */
    private static String verifyPreferencePersistence(Proof proof) {
        boolean ok = true;
        StringBuilder report = new StringBuilder("termLabels-prefs:");
        // master switch: toggle through the real click path (handler + save), read it back
        boolean display = termLabelMenu.isDisplayLabelsSelected();
        termLabelMenu.clickDisplayLabels();
        ok &= termLabelMenu.isDisplayLabelsSelected() == !display;
        ok &= TermLabelMenuF.readDisplaySelected(display) == !display;
        report.append(" display=").append(TermLabelMenuF.readDisplaySelected(display));
        // one label item (when the loaded proof supports one): toggle there and back, checking
        // the state AND the stored preference each way — the click path saves like Swing
        List<Name> names = TermLabelVisibilityManager.getSortedTermLabelNames(proof);
        if (!names.isEmpty()) {
            Name label = names.get(0);
            boolean labelState = termLabelMenu.isLabelSelected(label);
            termLabelMenu.clickLabel(label);
            ok &= termLabelMenu.isLabelSelected(label) == !labelState;
            ok &= TermLabelMenuF.readLabelSelected(label, labelState) == !labelState;
            report.append(" label=").append(!labelState);
            termLabelMenu.clickLabel(label);
            ok &= termLabelMenu.isLabelSelected(label) == labelState;
            ok &= TermLabelMenuF.readLabelSelected(label, !labelState) == labelState;
        } else {
            report.append(" label=skipped");
        }
        // restore the master switch (the click path also restores the saved preference)
        termLabelMenu.clickDisplayLabels();
        ok &= termLabelMenu.isDisplayLabelsSelected() == display;
        ok &= TermLabelMenuF.readDisplaySelected(display) == display;
        report.append(' ').append(ok ? "PASS" : "FAIL");
        return report.toString();
    }

    /** @return the next node in pre-order (node itself first), {@code null} after the last */
    private static Node nextPreorderNode(Node node) {
        if (node.childrenCount() > 0) {
            return node.child(0);
        }
        Node current = node;
        while (current.parent() != null) {
            Node parent = current.parent();
            int index = parent.getChildNr(current);
            if (index + 1 < parent.childrenCount()) {
                return parent.child(index + 1);
            }
            current = parent;
        }
        return null;
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
        // prefer a node whose sequent carries origin labels (nodes from the interactive part of
        // the saved proofs do; the root usually does not)
        Node originNode = null;
        for (Node n = node.proof().root(); n != null; n = nextPreorderNode(n)) {
            if ((!n.sequent().succedent().isEmpty() && OriginTermLabel
                    .getOrigin(new PosInOccurrence(n.sequent().succedent().getFirst(),
                        org.key_project.logic.PosInTerm.getTopLevel(), false)) != null)
                    || (!n.sequent().antecedent().isEmpty() && OriginTermLabel.getOrigin(
                        new PosInOccurrence(n.sequent().antecedent().getFirst(),
                            org.key_project.logic.PosInTerm.getTopLevel(), true)) != null)) {
                originNode = n;
                break;
            }
        }
        if (originNode != null) {
            node = originNode;
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
