/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.goallist;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.control.MenuItem;
import javafx.scene.control.OverrunStyle;
import javafx.scene.control.Tooltip;
import javafx.scene.input.ContextMenuEvent;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;

import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.GoalListener;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Name;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * First JavaFX version of the goal list, the counter-part of
 * {@code de.uka.ilkd.key.gui.GoalList} (a Swing {@code JList<Goal>}) in the module {@code key.ui}.
 * <p>
 * <b>Milestone M2, first version.</b> The list shows the open goals ({@link Proof#openGoals()})
 * of the selected proof. Like the Swing original, the view observes the selection model: a proof
 * change rebuilds the list; a node change re-highlights the selected goal and rebuilds the list
 * only when the displayed goal set actually differs from the proof's open goals (compared by
 * identity and size). This re-entrancy guard keeps a click-driven goal selection
 * ({@code setSelectedGoal} fires a node change) from wiping and rebuilding the list under the
 * user's cursor. Clicking a row selects the goal in the {@link KeYSelectionModel}; the ListView
 * selection is kept in sync with the model's selected goal.
 * <p>
 * A cell shows the node serial ({@code #n}), an automatic/interactive/linked marker (text
 * analogue of the key-hole icons of the Swing {@code IconCellRenderer}), and a one-line printed
 * sequent truncated to {@value #MAX_DISPLAYED_SEQUENT_LENGTH} characters, exactly like the Swing
 * renderer. The sequent text is produced by the core pretty printer
 * ({@link SequentViewLogicPrinter} with {@link NotationInfo} and the proof's {@code Services},
 * no term labels), cached per goal node.
 * <p>
 * Style classes (see {@code key-light.css} / {@code key-dark.css}, section "goal list view"):
 * {@code .goal-list} (the ListView), {@code .goal-list-cell} (every cell), the marker classes
 * {@code .goal-list-automatic}, {@code .goal-list-interactive}, {@code .goal-list-linked},
 * {@code .goal-list-label}, {@code .goal-list-marker}, {@code .goal-list-sequent},
 * {@code .goal-list-empty} (placeholder) and {@code .goal-list-header} (driver header). The
 * selected row is highlighted via the JavaFX pseudo class {@code .goal-list-cell:selected}.
 * <p>
 * Deliberately deferred to later M2/M3 chunks: live goal updates via
 * {@code ProofTreeListener}/{@code AutoModeListener} (currently updates piggyback on selection
 * events), the popup menu with the {@code DisableGoal} actions, keyboard shortcuts, and the
 * SelectingGoalListModel filtering.
 */
public class GoalListViewF extends ListView<Goal> {

    private static final Logger LOGGER = LoggerFactory.getLogger(GoalListViewF.class);

    /**
     * Maximum number of characters of the printed sequent shown in a cell, mirroring
     * {@code GoalList.MAX_DISPLAYED_SEQUENT_LENGTH} of the Swing view.
     */
    private static final int MAX_DISPLAYED_SEQUENT_LENGTH = 100;

    /**
     * Visible term labels of the first version: none. The goal list prints the bare sequent like
     * the Swing {@code GoalList.seqToString}.
     */
    private static final VisibleTermLabels NO_VISIBLE_TERM_LABELS = new VisibleTermLabels() {
        @Override
        public boolean contains(TermLabel label) {
            return false;
        }

        @Override
        public boolean contains(Name name) {
            return false;
        }
    };

    /**
     * Cache of the printed one-line sequent texts, keyed by the goal's node. A node's sequent is
     * immutable once created, and nodes are unique per identity, so an identity map is safe.
     * Cleared whenever another proof is displayed.
     */
    private final Map<Node, String> sequentTextCache = new IdentityHashMap<>();

    private KeYSelectionModel selectionModel;
    private Proof proof;
    /** true while this view mutates the items or the ListView selection programmatically */
    private boolean updatingSelection;

    /** guards against queueing more than one pending goal state refresh (see the listener) */
    private boolean goalStateRefreshPending;

    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        @Override
        public void selectedNodeChanged(KeYSelectionEvent<Node> event) {
            // A goal selection re-fires a node change: rebuild only when the displayed goal set
            // really differs from the proof's open goals, otherwise just re-highlight.
            if (displayedGoalsDifferFromProof()) {
                rebuild(proof);
            } else {
                highlightSelectedGoal();
            }
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
            rebuild(event.getSource().getSelectedProof());
        }
    };

    /**
     * Creates an empty goal list.
     */
    public GoalListViewF() {
        getStyleClass().add("goal-list");
        setCellFactory(view -> new GoalListCell());
        setPlaceholder(emptyPlaceholder());
        getSelectionModel().selectedItemProperty()
                .addListener((obs, oldItem, newItem) -> handleListSelection(newItem));
    }

    /**
     * Re-renders the rows when a goal's automatic state changes from anywhere (the goal list
     * popup, the proof tree popup, ...). The listener is attached to the displayed goals on
     * rebuild; only {@code automaticStateChanged} is handled, sequent changes are covered by the
     * proof-level rebuilds. Several goals can change in one batch (the proof tree popup disables
     * a whole subtree), so the refreshes are coalesced.
     */
    private final GoalListener goalStateListener = new GoalListener() {
        @Override
        public void automaticStateChanged(Goal source, boolean oldAutomatic,
                boolean newAutomatic) {
            if (goalStateRefreshPending) {
                return;
            }
            goalStateRefreshPending = true;
            FxUtil.runLater(() -> {
                goalStateRefreshPending = false;
                refreshAfterGoalStateChange();
            });
        }

        @Override
        public void sequentChanged(Goal source, SequentChangeInfo sci) {
            // covered by the proof-level rebuilds
        }

        @Override
        public void goalReplaced(Goal source, Node parent, ImmutableList<Goal> newGoals) {
            // covered by the proof-level rebuilds
        }
    };

    /**
     * Registers this view as a selection listener on the given model and shows the open goals of
     * the currently selected proof, if any.
     *
     * @param model the selection model to observe
     */
    public void attach(KeYSelectionModel model) {
        Objects.requireNonNull(model);
        if (selectionModel == model) {
            return;
        }
        if (selectionModel != null) {
            selectionModel.removeKeYSelectionListener(selectionListener);
        }
        selectionModel = model;
        model.addKeYSelectionListenerChecked(selectionListener);
        setProof(model.getSelectedProof());
    }

    /**
     * Shows the open goals of the given proof, replacing any previously shown list.
     *
     * @param newProof the proof to display, may be {@code null}
     */
    public void setProof(Proof newProof) {
        rebuild(newProof);
    }

    /**
     * Development self-test (M2): verifies that the rendered goal items are exactly the open
     * goals of the displayed proof (identity and order) and that the ListView selection is in
     * sync with the selection model's selected goal.
     *
     * @return a one-line report, {@code "... PASS"} if the list is consistent
     */
    public String verifyGoalList() {
        if (!FxUtil.isFxThread()) {
            return FxUtil.callAndWait(this::verifyGoalList);
        }
        if (proof == null) {
            return "no proof";
        }
        int openGoals = proof.openGoals().size();
        int rendered = getItems().size();
        boolean sameGoals = rendered == openGoals;
        int index = 0;
        for (Goal goal : proof.openGoals()) {
            if (index >= rendered || getItems().get(index) != goal) {
                sameGoals = false;
                break;
            }
            index++;
        }
        Goal selected = selectionModel != null ? selectionModel.getSelectedGoal() : null;
        boolean selectedInSync = getSelectionModel().getSelectedItem() == selected;
        boolean pass = sameGoals && selectedInSync;
        return "proofNodes=" + countProofNodes() + " openGoals=" + openGoals + " rendered="
            + rendered + " selectedInSync=" + selectedInSync + " " + (pass ? "PASS" : "FAIL");
    }

    private int countProofNodes() {
        int count = 0;
        for (Iterator<Node> it = proof.root().subtreeIterator(); it.hasNext();) {
            it.next();
            count++;
        }
        return count;
    }

    private void rebuild(Proof newProof) {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(() -> rebuild(newProof));
            return;
        }
        if (proof != newProof) {
            sequentTextCache.clear();
        }
        detachGoalStateListener();
        proof = newProof;
        updatingSelection = true;
        try {
            if (proof == null || proof.isDisposed()) {
                getItems().clear();
                setPlaceholder(emptyPlaceholder());
            } else {
                List<Goal> goals = new ArrayList<>();
                for (Goal goal : proof.openGoals()) {
                    goals.add(goal);
                }
                getItems().setAll(goals);
                attachGoalStateListener(goals);
                setPlaceholder(goals.isEmpty() ? closedPlaceholder() : emptyPlaceholder());
            }
            highlightSelectedGoal();
        } finally {
            updatingSelection = false;
        }
    }

    /** Stops observing the goals that are currently displayed, before the items are replaced. */
    private void detachGoalStateListener() {
        for (Goal goal : getItems()) {
            goal.removeGoalListener(goalStateListener);
        }
    }

    /** Observes the displayed goals for automatic state changes (see {@code goalStateListener}). */
    private void attachGoalStateListener(List<Goal> goals) {
        for (Goal goal : goals) {
            goal.addGoalListener(goalStateListener);
        }
    }

    /**
     * @return whether the currently displayed goals differ from the open goals of the displayed
     *         proof (identity and size comparison, cheap enough to run on every selection event)
     */
    private boolean displayedGoalsDifferFromProof() {
        if (proof == null || proof.isDisposed()) {
            return !getItems().isEmpty();
        }
        var openGoals = proof.openGoals();
        if (openGoals.size() != getItems().size()) {
            return true;
        }
        int index = 0;
        for (Goal goal : openGoals) {
            if (goal != getItems().get(index++)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Selects the model's selected goal in the ListView (or clears the selection when no goal is
     * selected, e.g. for an inner node). Mirrors {@code GoalList.selectSelectedGoal}.
     */
    private void highlightSelectedGoal() {
        Goal selected = selectionModel != null ? selectionModel.getSelectedGoal() : null;
        if (getSelectionModel().getSelectedItem() == selected) {
            return;
        }
        updatingSelection = true;
        try {
            if (selected == null) {
                getSelectionModel().clearSelection();
            } else {
                int index = getItems().indexOf(selected);
                if (index >= 0) {
                    getSelectionModel().select(index);
                    scrollTo(index);
                } else {
                    getSelectionModel().clearSelection();
                }
            }
        } finally {
            updatingSelection = false;
        }
    }

    private void handleListSelection(Goal newItem) {
        if (updatingSelection || newItem == null || selectionModel == null) {
            return;
        }
        if (newItem != selectionModel.getSelectedGoal()) {
            selectionModel.setSelectedGoal(newItem);
        }
    }

    /**
     * Shows the goal popup on the given goal (Swing {@code GoalList.popupMenu}, rebuilt on every
     * open): toggles the automatic/interactive state of the goal itself or of all other goals.
     * Swing's right-click handler selects the row under the pointer first, which the cell does
     * before calling this.
     */
    private void showGoalPopup(Goal goal, ContextMenuEvent e) {
        if (goal == null) {
            return;
        }
        ContextMenu menu = new ContextMenu();

        // DisableSingleGoal: the label flips with the goal's state, the action toggles it; the
        // row re-render happens through the goal state listener
        MenuItem single = new MenuItem(goal.isAutomatic() ? "Interactive Goal" : "Automatic Goal");
        single.setOnAction(ev -> goal.setEnabled(!goal.isAutomatic()));

        // DisableOtherGoals: all other goals get the opposite of this goal's state; Swing
        // enables the action only when the model holds more than one goal
        MenuItem others = new MenuItem(
            goal.isAutomatic() ? "Set Other Goals Interactive" : "Set Other Goals Automatic");
        others.setDisable(getItems().size() <= 1);
        others.setOnAction(ev -> {
            boolean enable = !goal.isAutomatic();
            for (Goal other : getItems()) {
                if (other != goal) {
                    other.setEnabled(enable);
                }
            }
        });

        menu.getItems().addAll(single, others);
        menu.show(this, e.getScreenX(), e.getScreenY());
        e.consume();
    }

    /**
     * Re-renders the rows after a goal state change: the items are re-set from the proof so every
     * cell recomputes marker text and style. Invoked by {@code goalStateListener}; keeping the
     * selection.
     */
    private void refreshAfterGoalStateChange() {
        if (proof == null || proof.isDisposed()) {
            return;
        }
        List<Goal> goals = new ArrayList<>();
        for (Goal goal : proof.openGoals()) {
            goals.add(goal);
        }
        updatingSelection = true;
        try {
            Goal selected = getSelectionModel().getSelectedItem();
            getItems().setAll(goals);
            if (selected != null) {
                int index = getItems().indexOf(selected);
                if (index >= 0) {
                    getSelectionModel().select(index);
                }
            }
        } finally {
            updatingSelection = false;
        }
    }

    /**
     * @return the one-line printed sequent text of the goal (truncated, no term labels), cached
     *         per goal node
     */
    private String sequentText(Goal goal) {
        Node node = goal.node();
        String cached = sequentTextCache.get(node);
        if (cached != null) {
            return cached;
        }
        String res;
        try {
            SequentViewLogicPrinter printer =
                SequentViewLogicPrinter.purePrinter(new NotationInfo(),
                    node.proof().getServices(), NO_VISIBLE_TERM_LABELS);
            printer.setMaxChar(MAX_DISPLAYED_SEQUENT_LENGTH);
            printer.printSequent(goal.sequent());
            // read the result only after printing has completed (see Swing GoalList.seqToString)
            res = printer.result().replace('\n', ' ');
            if (res.length() > MAX_DISPLAYED_SEQUENT_LENGTH) {
                res = res.substring(0, MAX_DISPLAYED_SEQUENT_LENGTH) + "...";
            }
        } catch (Exception ex) {
            LOGGER.warn("Goal list: problem printing the sequent of node #{}", node.serialNr(), ex);
            res = "<unable to print sequent>";
        }
        sequentTextCache.put(node, res);
        return res;
    }

    /**
     * @return the marker text of the goal, the text analogue of the icon choice of the Swing
     *         {@code IconCellRenderer} (linked, key-hole for automatic, disabled key-hole for
     *         interactive)
     */
    private static String markerText(Goal goal) {
        if (goal.isLinked()) {
            return "linked";
        }
        return goal.isAutomatic() ? "automatic" : "interactive";
    }

    /**
     * @return the style class highlighting the marker of the goal
     */
    private static String markerStyleClass(Goal goal) {
        if (goal.isLinked()) {
            return "goal-list-linked";
        }
        return goal.isAutomatic() ? "goal-list-automatic" : "goal-list-interactive";
    }

    private static Label emptyPlaceholder() {
        Label placeholder = new Label("No proof loaded.\n"
            + "Start with -Dkey.fx.demo.sequent=<file.key> to try the goal list.");
        placeholder.getStyleClass().add("goal-list-empty");
        placeholder.setWrapText(true);
        placeholder.setFont(ConfigF.DEFAULT.systemFont());
        return placeholder;
    }

    /** placeholder shown while a proof is selected but all of its goals are closed. */
    private static Label closedPlaceholder() {
        Label placeholder = new Label("No open goals — the proof is closed.");
        placeholder.getStyleClass().add("goal-list-empty");
        placeholder.setWrapText(true);
        placeholder.setFont(ConfigF.DEFAULT.systemFont());
        return placeholder;
    }

    /**
     * The cell rendering: node serial, goal marker, one-line sequent; selected state comes from
     * the ListView selection (styled via {@code .goal-list-cell:selected}).
     */
    private final class GoalListCell extends ListCell<Goal> {
        private final Label nameLabel = new Label();
        private final Label markerLabel = new Label();
        private final Label sequentLabel = new Label();
        private final HBox content;

        GoalListCell() {
            nameLabel.getStyleClass().add("goal-list-label");
            markerLabel.getStyleClass().add("goal-list-marker");
            sequentLabel.getStyleClass().add("goal-list-sequent");
            nameLabel.setFont(ConfigF.DEFAULT.systemFont());
            markerLabel.setFont(ConfigF.DEFAULT.systemFont());
            sequentLabel.setFont(ConfigF.DEFAULT.monoFont());
            // keep the node serial and the marker at their preferred size: only the sequent
            // label shrinks and ellipsizes when the cell is too narrow
            nameLabel.setMinWidth(Region.USE_PREF_SIZE);
            markerLabel.setMinWidth(Region.USE_PREF_SIZE);
            sequentLabel.setMaxWidth(Double.MAX_VALUE);
            sequentLabel.setTextOverrun(OverrunStyle.ELLIPSIS);
            HBox.setHgrow(sequentLabel, Priority.ALWAYS);
            content = new HBox(6, nameLabel, markerLabel, sequentLabel);
            // Swing GoalList's mouse listener selects the row under the pointer before the popup
            // opens; the popup acts on the (now selected) goal
            setOnContextMenuRequested(e -> {
                if (getItem() != null && getListView() != null) {
                    getListView().getSelectionModel().select(getIndex());
                    showGoalPopup(getItem(), e);
                }
            });
        }

        /**
         * Clamps the preferred cell width to the width of the ListView so that long sequents
         * ellipsize (see the sequent label) instead of growing a horizontal scrollbar.
         */
        @Override
        protected double computePrefWidth(double height) {
            double pref = super.computePrefWidth(height);
            ListView<Goal> listView = getListView();
            if (listView == null || listView.getWidth() <= 0) {
                return pref;
            }
            return Math.min(pref, Math.max(listView.getWidth() - 12, 100));
        }

        @Override
        protected void updateItem(Goal goal, boolean empty) {
            super.updateItem(goal, empty);
            getStyleClass().clear();
            getStyleClass().add("goal-list-cell");
            if (empty || goal == null) {
                setGraphic(null);
                setText(null);
                setTooltip(null);
                return;
            }
            String text = sequentText(goal);
            String marker = markerText(goal);
            markerLabel.getStyleClass().setAll("goal-list-marker", markerStyleClass(goal));
            nameLabel.setText("#" + goal.node().serialNr());
            markerLabel.setText(marker);
            sequentLabel.setText(text);
            setGraphic(content);
            setText(null);
            setTooltip(new Tooltip("Node #" + goal.node().serialNr() + " (" + marker + ")\n"
                + text));
        }
    }
}
