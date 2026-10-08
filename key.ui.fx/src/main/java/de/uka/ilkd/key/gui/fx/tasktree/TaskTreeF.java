/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tasktree;

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Objects;
import javafx.collections.ListChangeListener;
import javafx.scene.control.Label;
import javafx.scene.control.Tooltip;
import javafx.scene.control.TreeCell;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.layout.BorderPane;

import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.proofmanagement.ProofManagementDialogF.StatusKind;
import de.uka.ilkd.key.gui.fx.proofmanagement.ProofManagerF;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;

import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * JavaFX port of the Swing "Loaded Proofs" view ({@code de.uka.ilkd.key.gui.TaskTree}, module
 * {@code key.ui}): a tree of the currently loaded proofs, grouped by their proof environment
 * (the Swing {@code TaskTreeModel} {@code EnvNode}s). Each proof row shows the proof name, the
 * number of open goals and the proof status icon (the key-hole icons of the Swing
 * {@code TaskTreeIconCellRenderer}, TaskTree.java:348-394, expressed as CSS-colored font icons).
 * Clicking a proof row activates it (Swing {@code problemChosen},
 * TaskTree.java:194-200: {@code selectionModel.setSelectedProof}, routed through
 * {@link ProofManagerF#setActive(Proof)}), a change of the selected proof highlights the
 * corresponding row (Swing {@code TaskTreeSelectionListener}, TaskTree.java:397-415).
 * <p>
 * The multi-proof state (the list of proofs and the active one) lives in
 * {@link ProofManagerF}, which the main window consults on every load and the Proof Management
 * dialog reports started proofs to; this view binds to the manager's observable list.
 * <p>
 * This first version is a flat two-level tree (environment → proofs); the full Swing model port
 * ({@code TaskTreeModel} with {@code BasicTask}/{@code ProofAggregateTask} compound tasks and
 * the right-click context menu with close/prune/save actions, TaskTree.java:273-312) is
 * deferred. Like the Swing view, proof structure events ({@code proofClosed}/{@code
 * proofPruned}/{@code proofStructureChanged}) refresh the affected row
 * (TaskTree.java:318-345).
 */
public class TaskTreeF extends BorderPane {

    private static final Logger LOGGER = LoggerFactory.getLogger(TaskTreeF.class);

    /** the multi-proof state consulted by the main window (proofmgmt). */
    private final ProofManagerF proofManager;

    /** tree item values: either a {@link ProofEnvironment} group or a {@link Proof} */
    private final TreeView<Object> tree = new TreeView<>();

    /** environment group items by environment (identity, environments are singletons per env) */
    private final Map<ProofEnvironment, TreeItem<Object>> envItems = new IdentityHashMap<>();

    /** proof items by proof */
    private final Map<Proof, TreeItem<Object>> proofItems = new IdentityHashMap<>();

    /** proof tree listeners per registered proof (row refresh on structural changes) */
    private final Map<Proof, ProofTreeListener> proofListeners = new IdentityHashMap<>();

    private @Nullable KeYSelectionModel selectionModel;

    /** true while this view mutates the tree selection programmatically */
    private boolean updatingSelection;

    /**
     * The selection listener keeping the tree selection in sync with the mediator's selected
     * proof (Swing {@code TaskTreeSelectionListener}).
     */
    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        @Override
        public void selectedNodeChanged(KeYSelectionEvent<de.uka.ilkd.key.proof.Node> event) {
            // empty (like the Swing listener)
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
            Proof selected = event.getSource().getSelectedProof();
            proofManager.setActiveFromSelection(selected);
            syncSelection(selected);
        }
    };

    /**
     * Creates the loaded proofs view bound to the given multi-proof state.
     *
     * @param proofManager the proof manager of the main window
     */
    public TaskTreeF(ProofManagerF proofManager) {
        this.proofManager = proofManager;
        tree.getStyleClass().add("loaded-proofs");
        tree.setShowRoot(false);
        tree.setRoot(new TreeItem<>("Tasks"));
        tree.setCellFactory(view -> new TaskTreeCell());
        tree.getSelectionModel().selectedItemProperty().addListener((obs, old, value) -> {
            if (updatingSelection || value == null || !(value.getValue() instanceof Proof proof)) {
                return;
            }
            // a user click activates the proof (Swing TaskTreeSelectionListener → problemChosen)
            if (selectionModel != null && selectionModel.getSelectedProof() != proof) {
                LOGGER.debug("Loaded Proofs: activating proof {}", proof.name());
                proofManager.setActive(proof);
            }
        });
        Label placeholder = new Label("No proofs loaded.");
        placeholder.getStyleClass().add("loaded-proofs-empty");
        setCenter(tree);
        setBottom(placeholder);

        // the view follows the multi-proof state of the manager: every proof registered by the
        // main window (or the Proof Management dialog) gets a row
        proofManager.proofs().addListener((ListChangeListener<Proof>) change -> {
            while (change.next()) {
                if (change.wasAdded()) {
                    change.getAddedSubList().forEach(this::addProof);
                }
                if (change.wasRemoved()) {
                    change.getRemoved().forEach(this::removeProof);
                }
            }
        });
    }

    /**
     * Registers this view as a selection listener on the given model and highlights the
     * currently selected proof.
     *
     * @param model the selection model of the mediator
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
        syncSelection(model.getSelectedProof());
    }

    /**
     * Adds a loaded proof to the view (Swing {@code TaskTree.addProof}, TaskTree.java:112-123).
     * The proof is grouped below its proof environment; the environment group is expanded. The
     * proof is observed for structural changes so its row status stays current.
     *
     * @param proof the loaded proof
     */
    private void addProof(Proof proof) {
        if (proofItems.containsKey(proof)) {
            LOGGER.debug("Loaded Proofs: proof {} already shown", proof.name());
            return;
        }
        TreeItem<Object> envItem = envItemFor(proof.getEnv());
        TreeItem<Object> proofItem = new TreeItem<>(proof);
        envItem.getChildren().add(proofItem);
        envItem.setExpanded(true);
        proofItems.put(proof, proofItem);

        // observe structural changes of the proof (Swing TaskTreeProofTreeListener repaints the
        // affected row, TaskTree.java:318-345; here the cell re-renders on tree refresh)
        ProofTreeListener listener = new ProofTreeAdapter() {
            private void refreshRow(ProofTreeEvent e) {
                FxUtil.runLater(() -> {
                    TreeItem<Object> item = proofItems.get(e.getSource());
                    if (item != null) {
                        // re-render the cell contents (status/goal count may have changed)
                        tree.refresh();
                    }
                });
            }

            @Override
            public void proofClosed(ProofTreeEvent e) {
                refreshRow(e);
            }

            @Override
            public void proofPruned(ProofTreeEvent e) {
                refreshRow(e);
            }

            @Override
            public void proofStructureChanged(ProofTreeEvent e) {
                refreshRow(e);
            }
        };
        proof.addProofTreeListener(listener);
        proofListeners.put(proof, listener);

        refreshEmptyState();
    }

    /**
     * Removes a proof from the view (Swing {@code TaskTree.removeProof}, TaskTree.java:241-267).
     *
     * @param proof the proof to remove, may be {@code null}
     */
    private void removeProof(@Nullable Proof proof) {
        if (proof == null) {
            return;
        }
        ProofTreeListener listener = proofListeners.remove(proof);
        if (listener != null) {
            proof.removeProofTreeListener(listener);
        }
        TreeItem<Object> item = proofItems.remove(proof);
        if (item == null) {
            return;
        }
        TreeItem<Object> parent = item.getParent();
        parent.getChildren().remove(item);
        if (parent.getChildren().isEmpty() && parent.getParent() != null) {
            // remove the empty environment group (Swing TaskTreeModel.removeTask)
            envItems.remove((ProofEnvironment) parent.getValue());
            parent.getParent().getChildren().remove(parent);
        }
        refreshEmptyState();
    }

    /**
     * @return the number of proofs currently shown
     */
    public int getProofCount() {
        return proofItems.size();
    }

    /**
     * Development self test (the {@code key.fx.verify.proofmgmt} affordance): verifies that
     * every registered proof has a row with the expected goal count in the label and that the
     * highlighted row is the selected proof.
     *
     * @return a one-line report, {@code "... PASS"} if all checks pass
     */
    public String verifyContent() {
        if (!FxUtil.isFxThread()) {
            return FxUtil.callAndWait(this::verifyContent);
        }
        for (Map.Entry<Proof, TreeItem<Object>> e : proofItems.entrySet()) {
            Proof proof = e.getKey();
            TreeItem<Object> item = e.getValue();
            if (item.getParent() == null) {
                return "proof row of " + proof.name() + " is detached FAIL";
            }
            String expected = labelFor(proof);
            String rendered = cellText(item);
            if (!expected.equals(rendered)) {
                return "row text '" + rendered + "' != '" + expected + "' FAIL";
            }
        }
        Proof selected = selectionModel != null ? selectionModel.getSelectedProof() : null;
        if (selected != null && proofItems.containsKey(selected)) {
            TreeItem<Object> item = tree.getSelectionModel().getSelectedItem();
            if (item == null || item.getValue() != selected) {
                return "highlighted row is not the selected proof FAIL";
            }
        }
        return "proofs=" + proofItems.size() + " rows in sync PASS";
    }

    private String cellText(TreeItem<Object> item) {
        // the rendered text is recomputed exactly like the cell does it (the row is rendered
        // fresh on every refresh, so the model text is the rendered text)
        return item.getValue() instanceof Proof proof ? labelFor(proof) : "";
    }

    private String labelFor(Proof proof) {
        return proof.name() + " · " + proof.openGoals().size() + " open goal(s)";
    }

    private TreeItem<Object> envItemFor(ProofEnvironment env) {
        return envItems.computeIfAbsent(env, e -> {
            TreeItem<Object> item = new TreeItem<>(e);
            tree.getRoot().getChildren().add(item);
            item.setExpanded(true);
            return item;
        });
    }

    private void refreshEmptyState() {
        boolean empty = proofItems.isEmpty();
        getBottom().setVisible(empty);
        getBottom().setManaged(empty);
    }

    /**
     * Highlights the row of the given proof (Swing
     * {@code TaskTreeSelectionListener.selectedProofChanged}, TaskTree.java:406-413).
     */
    private void syncSelection(@Nullable Proof proof) {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(() -> syncSelection(proof));
            return;
        }
        if (proof == null) {
            return;
        }
        TreeItem<Object> item = proofItems.get(proof);
        if (item == null) {
            return;
        }
        updatingSelection = true;
        try {
            tree.getSelectionModel().clearSelection();
            tree.getSelectionModel().select(item);
            tree.scrollTo(tree.getRow(item));
        } finally {
            updatingSelection = false;
        }
    }

    /**
     * The tree cell (Swing {@code TaskTreeIconCellRenderer}, TaskTree.java:348-394): the
     * key-hole status icon, the proof name with the open goal count for proof rows, the
     * environment description for group rows.
     */
    private static final class TaskTreeCell extends TreeCell<Object> {
        @Override
        protected void updateItem(Object item, boolean empty) {
            super.updateItem(item, empty);
            getStyleClass().removeIf("loaded-proofs-env"::equals);
            if (empty || item == null) {
                setText(null);
                setGraphic(null);
                setTooltip(null);
                return;
            }
            if (item instanceof ProofEnvironment env) {
                getStyleClass().add("loaded-proofs-env");
                setText(env.description());
                setGraphic(null);
                setTooltip(null);
                return;
            }
            Proof proof = (Proof) item;
            StatusKind kind = StatusKind.fromProofStatus(proof.mgt().getStatus());
            setText(labelText(proof));
            javafx.scene.Node icon =
                kind == StatusKind.NONE ? null
                        : IconFactoryF.createIcon(IconFactoryF.Key.KEY_HOLE, 14);
            if (icon != null && kind.styleClass() != null) {
                icon.getStyleClass().add(kind.styleClass());
                if (kind.tooltip() != null) {
                    setTooltip(new Tooltip(kind.tooltip()));
                }
            }
            setGraphic(icon);
        }

        private static String labelText(Proof proof) {
            return proof.name() + " · " + proof.openGoals().size() + " open goal(s)";
        }
    }
}
