/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.originlabels;

import java.util.Comparator;
import java.util.Map;
import java.util.TreeMap;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.Menu;
import javafx.scene.control.SeparatorMenuItem;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerListener;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Name;

/**
 * JavaFX port of the Swing {@code de.uka.ilkd.key.gui.actions.TermLabelMenu} (View menu "Term
 * Labels"): a submenu with the "Display Term Labels in Formulas" check item and one check item
 * per term label name supported by the loaded proof, controlling a shared
 * {@link TermLabelVisibilityManager} that the sequent view printer consults.
 * <p>
 * Behavioural parity with the Swing original:
 * <ul>
 * <li>The visibility manager defaults to <em>show all labels</em> ({@code showLabels = true}),
 * except the labels listed in {@link TermLabelVisibilityManager}'s {@code ALWAYS_HIDDEN}
 * (currently {@code OriginTermLabel.NAME}, which is rendered by the origin visualizer instead).
 * So after installing this menu the sequent view prints the other term labels, like Swing.</li>
 * <li>Every change of the manager re-prints the view (Swing {@code MainWindow.makePrettyView}
 * from {@code handleVisibleLabelsChanged}); here the reprint is a {@link Runnable} provided by
 * the caller (the FX main window re-prints its sequent view).</li>
 * <li>The label items are rebuilt when the selected proof changes (Swing {@code rebuildMenu} in
 * {@code selectedProofChanged}), because the available label names depend on the proof's
 * profile ({@code TermLabelVisibilityManager.getSortedTermLabelNames}). The Swing original
 * additionally bolds the items whose labels occur in the displayed sequent — a cosmetic
 * affordance that is not ported.</li>
 * </ul>
 *
 * @author lanzinger (Swing original), the key.ui.fx team (port)
 */
public class TermLabelMenuF extends Menu {

    /** The submenu title (Swing {@code TermLabelMenu.TERM_LABEL_MENU}). */
    public static final String TERM_LABEL_MENU = "Term Labels";

    /** the shared visibility state consulted by the sequent view printer. */
    private final TermLabelVisibilityManager visibleTermLabels = new TermLabelVisibilityManager();

    /** the per-label check items, keyed by label name (Swing {@code checkBoxMap}). */
    private final Map<Name, CheckMenuItem> checkBoxMap =
        new TreeMap<>(Comparator.comparing(Name::toString));

    /**
     * the "Display Term Labels in Formulas" master switch (Swing {@code DisplayLabelsCheckBox}).
     */
    private final CheckMenuItem displayLabelsItem;

    /** re-prints the affected views (Swing {@code MainWindow.makePrettyView}). */
    private final Runnable reprint;

    /** Observes changes on {@link #visibleTermLabels}; created in the constructor. */
    private final TermLabelVisibilityManagerListener visibilityListener;

    /**
     * Creates the term labels submenu.
     *
     * @param reprint invoked whenever the label visibility changed and the views must re-render
     */
    public TermLabelMenuF(Runnable reprint) {
        this.reprint = reprint;
        setText(TERM_LABEL_MENU);

        displayLabelsItem = new CheckMenuItem("Display Term Labels in Formulas");
        displayLabelsItem.setSelected(visibleTermLabels.isShowLabels());
        displayLabelsItem.setOnAction(e -> visibleTermLabels
                .setShowLabels(displayLabelsItem.isSelected()));

        this.visibilityListener = e -> {
            displayLabelsItem.setSelected(visibleTermLabels.isShowLabels());
            for (Map.Entry<Name, CheckMenuItem> entry : checkBoxMap.entrySet()) {
                entry.getValue().setDisable(!visibleTermLabels.isShowLabels());
                entry.getValue().setSelected(!visibleTermLabels.isHidden(entry.getKey()));
            }
            reprint.run();
        };
        visibleTermLabels.addTermLabelVisibilityManagerListener(visibilityListener);

        getItems().addAll(displayLabelsItem, new SeparatorMenuItem());
    }

    /**
     * @return the shared visibility manager; hand it to the views' printers (Swing
     *         {@code MainWindow.getVisibleTermLabels})
     */
    public TermLabelVisibilityManager getVisibleTermLabels() {
        return visibleTermLabels;
    }

    /**
     * Rebuilds the per-label check items for the given proof (Swing {@code rebuildMenu},
     * triggered by the mediator's {@code selectedProofChanged}).
     *
     * @param proof the newly selected proof, may be {@code null} (only the master item remains)
     */
    public void rebuildMenu(Proof proof) {
        getItems().clear();
        getItems().addAll(displayLabelsItem, new SeparatorMenuItem());
        checkBoxMap.clear();
        if (proof == null) {
            return;
        }
        // sorted list of term label names supported by the proof's profile
        for (Name labelName : TermLabelVisibilityManager.getSortedTermLabelNames(proof)) {
            CheckMenuItem item = new CheckMenuItem(labelName.toString());
            item.setSelected(!visibleTermLabels.isHidden(labelName));
            item.setDisable(!visibleTermLabels.isShowLabels());
            item.setOnAction(
                e -> visibleTermLabels.setHidden(labelName, !item.isSelected()));
            checkBoxMap.put(labelName, item);
            getItems().add(item);
        }
    }

    /**
     * Detaches the visibility listener (called when the main window closes; Swing keeps the
     * listener because there is only one MainWindow).
     */
    public void dispose() {
        visibleTermLabels.removeTermLabelVisibilityManagerListener(visibilityListener);
    }
}
