/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.originlabels;

import java.util.Comparator;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.prefs.Preferences;
import javafx.geometry.Insets;
import javafx.scene.control.CheckBox;
import javafx.scene.control.CustomMenuItem;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.HBox;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerListener;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Name;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

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
 * profile ({@code TermLabelVisibilityManager.getSortedTermLabelNames}).</li>
 * <li>The check states are persisted (B17): the master switch and every label item write their
 * selected state to {@link Preferences} {@code userNodeForPackage(MainWindowF.class)} under the
 * exact Swing {@code AbstractButtonSaver} keys ({@code <SimpleName>.<name>.selected}, i.e.
 * {@code DisplayLabelsCheckBox.DisplayLabelsCheckBox.selected} and
 * {@code TermLabelCheckBox.<label>.selected}, PreferenceSaver.java:257-262); building the menu
 * reads the saved states back and applies them to the manager (Swing
 * {@code mainWindow.loadPreferences(this)} in the item constructors).</li>
 * </ul>
 * <p>
 * Styling parity (B17): the items are {@link CustomMenuItem}s wrapping an
 * {@code HBox(CheckBox, Label)} — the label carries the text, the tooltip and the bold/italic
 * occurrence font (JavaFX menu items have no tooltip or font API). Like Swing's
 * {@code selectedNodeChanged} listener the boldness marks the labels that occur in the currently
 * displayed sequent ({@link #applyStyles}), with the Swing tooltips ("Click to toggle visibility
 * for term label X." / "Term label X does not occur in the current sequent." / the disabled
 * hint). Unlike the Swing original the item creation re-runs the (re)loaded state through the
 * manager instead of only showing the manager state.
 *
 * @author lanzinger (Swing original), the key.ui.fx team (port)
 */
public class TermLabelMenuF extends Menu {

    /** The submenu title (Swing {@code TermLabelMenu.TERM_LABEL_MENU}). */
    public static final String TERM_LABEL_MENU = "Term Labels";

    /** the Swing {@code AbstractButtonSaver} preference node (PreferenceSaver.java:166). */
    private static final Preferences PREFS =
        Preferences.userNodeForPackage(MainWindowF.class);

    /** the shared visibility state consulted by the sequent view printer. */
    private final TermLabelVisibilityManager visibleTermLabels = new TermLabelVisibilityManager();

    /** the per-label check items, keyed by label name (Swing {@code checkBoxMap}). */
    private final Map<Name, TermLabelCheckBoxF> checkBoxMap =
        new TreeMap<>(Comparator.comparing(Name::toString));

    /**
     * the "Display Term Labels in Formulas" master switch (Swing {@code DisplayLabelsCheckBox}).
     */
    private final DisplayLabelsCheckBoxF displayLabelsItem;

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

        // the master switch: the persisted state wins over the manager default (Swing
        // DisplayLabelsCheckBox constructor: loadPreferences + setSelected)
        displayLabelsItem =
            new DisplayLabelsCheckBoxF(readDisplaySelected(true), this::applyDisplayToggle);

        this.visibilityListener = e -> {
            displayLabelsItem.setSelected(visibleTermLabels.isShowLabels());
            for (Map.Entry<Name, TermLabelCheckBoxF> entry : checkBoxMap.entrySet()) {
                TermLabelCheckBoxF item = entry.getValue();
                item.setEnabled(visibleTermLabels.isShowLabels());
                item.setSelected(!visibleTermLabels.isHidden(entry.getKey()));
            }
            reprint.run();
        };
        visibleTermLabels.addTermLabelVisibilityManagerListener(visibilityListener);

        // apply the loaded state (Swing loadPreferences -> the setSelected override -> the click
        // handler); fires the listener above when it differs from the manager default
        visibleTermLabels.setShowLabels(displayLabelsItem.isSelected());

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
     * triggered by the mediator's {@code selectedProofChanged}). Each new item reads its
     * persisted selected state and applies it to the manager (Swing {@code TermLabelCheckBox}
     * constructor: {@code loadPreferences} + {@code visibleTermLabels.setHidden(labelName,
     * !isSelected())}).
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
            TermLabelCheckBoxF item = new TermLabelCheckBoxF(labelName,
                readLabelSelected(labelName, !visibleTermLabels.isHidden(labelName)),
                () -> applyLabelToggle(labelName));
            // apply the (re)loaded state to the manager (Swing TermLabelCheckBox constructor)
            visibleTermLabels.setHidden(labelName, !item.isSelected());
            checkBoxMap.put(labelName, item);
            getItems().add(item);
        }
        // the fresh items fall back to the italic occurrence style until the selection syncs
    }

    /** the label item change handler (Swing {@code TermLabelCheckBox.handleClickEvent}). */
    private void applyLabelToggle(Name labelName) {
        TermLabelCheckBoxF item = checkBoxMap.get(labelName);
        if (item != null) {
            visibleTermLabels.setHidden(labelName, !item.isSelected());
        }
    }

    /** the master switch change handler (Swing {@code DisplayLabelsCheckBox.handleClickEvent}). */
    private void applyDisplayToggle() {
        visibleTermLabels.setShowLabels(displayLabelsItem.isSelected());
    }

    /**
     * Applies the occurrence font style + tooltip of every label item for the node currently
     * displayed in the sequent view (Swing {@code TermLabelMenu.selectedNodeChanged}): the
     * labels occurring in the node's sequent are bold ("Click to toggle visibility for term
     * label X."), the others italic ("Term label X does not occur in the current sequent.").
     *
     * @param node the selected node, may be {@code null}
     */
    public void applyStyles(Node node) {
        Set<Name> occurring = node == null ? Set.of() : getOccurringTermLabels(node.sequent());
        for (Map.Entry<Name, TermLabelCheckBoxF> entry : checkBoxMap.entrySet()) {
            entry.getValue().applyOccurrenceStyle(occurring.contains(entry.getKey()));
        }
    }

    /** @return the names of the term labels occurring in the given sequent (Swing recurse). */
    private static Set<Name> getOccurringTermLabels(Sequent seq) {
        Set<Name> result = new HashSet<>();
        for (SequentFormula sf : seq) {
            collectLabels((JTerm) sf.formula(), result);
        }
        return result;
    }

    private static void collectLabels(JTerm term, Set<Name> result) {
        if (term.hasLabels()) {
            for (TermLabel label : term.getLabels()) {
                result.add(label.name());
            }
        }
        for (org.key_project.logic.Term sub : term.subs()) {
            collectLabels((JTerm) sub, result);
        }
    }

    /** @return whether the master switch is selected (Swing {@code isSelected}) */
    boolean isDisplayLabelsSelected() {
        return displayLabelsItem.isSelected();
    }

    /**
     * Sets the master switch without saving (Swing {@code setSelected}); applies to the manager.
     */
    void setDisplayLabelsSelected(boolean selected) {
        displayLabelsItem.setSelected(selected);
    }

    /** The user-click path of the master switch (Swing actionPerformed: handler + save). */
    void clickDisplayLabels() {
        displayLabelsItem.click();
    }

    /** @return whether the given label item exists and is selected */
    boolean isLabelSelected(Name labelName) {
        TermLabelCheckBoxF item = checkBoxMap.get(labelName);
        return item != null && item.isSelected();
    }

    /** Sets one label item without saving (Swing {@code setSelected}); applies to the manager. */
    void setLabelSelected(Name labelName, boolean selected) {
        TermLabelCheckBoxF item = checkBoxMap.get(labelName);
        if (item != null) {
            item.setSelected(selected);
        }
    }

    /** The user-click path of one label item (Swing actionPerformed: handler + save). */
    void clickLabel(Name labelName) {
        TermLabelCheckBoxF item = checkBoxMap.get(labelName);
        if (item != null) {
            item.click();
        }
    }

    // ------------------------------------------------------------------
    // preferences (B17): the Swing AbstractButtonSaver key scheme
    // ------------------------------------------------------------------

    /** the AbstractButtonSaver key of a Swing check box (PreferenceSaver.java:260). */
    private static String buttonId(String simpleName, String componentName) {
        return simpleName + "." + componentName + ".selected";
    }

    /** the persisted master state, or {@code fallback} when nothing is stored yet. */
    static boolean readDisplaySelected(boolean fallback) {
        return PREFS.getBoolean(buttonId("DisplayLabelsCheckBox", "DisplayLabelsCheckBox"),
            fallback);
    }

    /** the persisted state of one label item, or {@code fallback} when nothing is stored yet. */
    static boolean readLabelSelected(Name labelName, boolean fallback) {
        return PREFS.getBoolean(buttonId("TermLabelCheckBox", labelName.toString()), fallback);
    }

    /** writes the master state (Swing {@code AbstractButtonSaver.save}). */
    static void writeDisplaySelected(boolean selected) {
        PREFS.putBoolean(buttonId("DisplayLabelsCheckBox", "DisplayLabelsCheckBox"), selected);
    }

    /** writes the state of one label item (Swing {@code AbstractButtonSaver.save}). */
    static void writeLabelSelected(Name labelName, boolean selected) {
        PREFS.putBoolean(buttonId("TermLabelCheckBox", labelName.toString()), selected);
    }

    /**
     * Detaches the visibility listener (called when the main window closes; Swing keeps the
     * listener because there is only one MainWindow).
     */
    public void dispose() {
        visibleTermLabels.removeTermLabelVisibilityManagerListener(visibilityListener);
    }

    /**
     * P3b/B17: one check row of the term labels menu (Swing {@code KeYMenuCheckBox}, a {@code
     * JCheckBoxMenuItem}): a {@link CustomMenuItem} whose content is an
     * {@code HBox(CheckBox, Label)} — the label carries the text and (for label items) the
     * tooltip and the bold/italic occurrence font, which JavaFX menu items cannot do. Clicking
     * the row or the checkbox applies the change and persists it (Swing
     * {@code actionPerformed -> handleClickEvent() + savePreferences}); {@link #setSelected}
     * applies a value without persisting (Swing's {@code setSelected} override, used by the
     * preference loading and by the visibility-manager sync). The menu stays open after a click,
     * like Swing's check menu items.
     */
    abstract static class CheckBoxMenuItemF extends CustomMenuItem {
        final CheckBox checkBox = new CheckBox();
        final Label label = new Label();
        private final Runnable onChange;

        CheckBoxMenuItemF(String text, boolean selected, Runnable onChange) {
            this.onChange = onChange;
            label.setText(text);
            checkBox.setSelected(selected);
            HBox row = new HBox(6, checkBox, label);
            row.setPadding(new Insets(0, 6, 0, 0));
            setContent(row);
            setHideOnClick(false);
            // direct checkbox clicks: the box is already toggled, apply + save
            checkBox.setOnAction(e -> {
                onChange.run();
                save();
            });
            // row clicks / keyboard activation: toggle the box, apply + save
            setOnAction(e -> {
                checkBox.setSelected(!checkBox.isSelected());
                onChange.run();
                save();
            });
        }

        /** @return the current state (Swing {@code isSelected}) */
        final boolean isSelected() {
            return checkBox.isSelected();
        }

        /** applies a value to the box and the model without saving (Swing {@code setSelected}). */
        final void setSelected(boolean selected) {
            checkBox.setSelected(selected);
            onChange.run();
        }

        /** the user-click path (Swing {@code actionPerformed}): toggles, applies and saves. */
        final void click() {
            checkBox.setSelected(!checkBox.isSelected());
            onChange.run();
            save();
        }

        /** persists the current state (Swing {@code mainWindow.savePreferences(checkBox)}). */
        abstract void save();
    }

    /**
     * P3b/B17: the "Display Term Labels in Formulas" master switch (Swing
     * {@code DisplayLabelsCheckBox}, name + class name {@code DisplayLabelsCheckBox}).
     */
    static final class DisplayLabelsCheckBoxF extends CheckBoxMenuItemF {
        DisplayLabelsCheckBoxF(boolean selected, Runnable onChange) {
            super("Display Term Labels in Formulas", selected, onChange);
            Tooltip.install(label, new Tooltip(
                "Use this checkbox to toggle visibility for all term labels."));
        }

        @Override
        void save() {
            writeDisplaySelected(isSelected());
        }
    }

    /**
     * P3b/B17: one label item (Swing {@code TermLabelCheckBox}, class name {@code
     * TermLabelCheckBox}). The bold/italic font style + tooltip mark whether the label occurs in
     * the currently displayed sequent ({@link #applyOccurrenceStyle}, Swing
     * {@code setBoldFont/setItalicFont}); the disabled tooltip follows Swing
     * {@code updateToolTipText}.
     */
    static final class TermLabelCheckBoxF extends CheckBoxMenuItemF {
        private final Name labelName;
        private String tooltipWhenEnabled;

        TermLabelCheckBoxF(Name labelName, boolean selected, Runnable onChange) {
            super(labelName.toString(), selected, onChange);
            this.labelName = labelName;
            // Swing TermLabelCheckBox constructor: setItalicFont() until the selection syncs
            applyOccurrenceStyle(false);
        }

        /** bold = the label occurs in the displayed sequent, italic otherwise (Swing). */
        void applyOccurrenceStyle(boolean occurs) {
            label.setStyle(occurs ? "-fx-font-weight: bold;" : "-fx-font-style: italic;");
            tooltipWhenEnabled = occurs
                    ? "Click to toggle visibility for term label " + labelName + "."
                    : "Term label " + labelName + " does not occur in the current sequent.";
            updateTooltip();
        }

        /** enables/disables the checkbox and updates the tooltip (Swing {@code setEnabled}). */
        void setEnabled(boolean enabled) {
            checkBox.setDisable(!enabled);
            updateTooltip();
        }

        private void updateTooltip() {
            String text = checkBox.isDisable()
                    ? "You turned off visibility for all term labels. This checkbox is disabled."
                    : tooltipWhenEnabled;
            Tooltip.install(label, new Tooltip(text));
        }

        @Override
        void save() {
            writeLabelSelected(labelName, isSelected());
        }
    }
}
