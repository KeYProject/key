/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.fx;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.control.TitledPane;
import javafx.scene.control.Tooltip;
import javafx.scene.control.TreeCell;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppListener;

import org.key_project.exploration.ExplorationNodeData;
import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.kordamp.ikonli.fontawesome6.FontAwesomeRegular;
import org.kordamp.ikonli.fontawesome6.FontAwesomeSolid;
import org.kordamp.ikonli.javafx.FontIcon;

/**
 * JavaFX port of the Swing {@code
 * org.key_project.exploration.ui.ExplorationStepsList} (ExplorationStepsList.java:36-410): a view
 * that summarises the exploration steps inside the current proof and lets the user jump to /
 * prune exploration nodes.
 * <p>
 * The port reproduces the Swing layout — a "List of Exploration" list on top of an "Explorations
 * in Proof" tree (the chain of exploration nodes found by the depth-first traversal), plus the
 * "Jump To Node" / "Prune selected exploration" buttons and the status-line indicator label — with
 * JavaFX controls.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b>
 * <ul>
 * <li>The Swing {@code Icons} class is AWT/Swing-bound — the tab title's help button is not
 * ported; the status indicator uses ikonli FontAwesome glyphs (solid vs. regular compass,
 * mirroring {@code Icons.EXPLORE}/{@code Icons.EXPLORE_DISABLE}) instead of the icon images.</li>
 * <li>Pruning goes through {@code MainWindowF.getUserInterfaceControl().getProofControl()} (the
 * FX counterpart of the Swing {@code mediator.getUI().getProofControl()}).</li>
 * </ul>
 */
@NullMarked
final class ExplorationStepsPanelF extends VBox {

    /**
     * status-line indicator icons (ikonli FontAwesome): the solid compass marks a proof with
     * exploration steps, the regular (outline) compass an empty one — the Swing
     * {@code Icons.EXPLORE}/{@code Icons.EXPLORE_DISABLE} pair
     */
    private final FontIcon hasStepsIcon = new FontIcon(FontAwesomeSolid.COMPASS);
    private final FontIcon noStepsIcon = new FontIcon(FontAwesomeRegular.COMPASS);

    /** the singleton status-line indicator label (Swing {@code hasExplorationSteps}) */
    private final Label hasExplorationSteps = new Label(null, noStepsIcon);
    /** the list of exploration nodes in traversal order (Swing {@code listModelExploration}) */
    private final ObservableList<Node> listModelExploration = FXCollections.observableArrayList();
    private final ListView<Node> listExplorations = new ListView<>(listModelExploration);
    /** the chain tree of exploration nodes (Swing {@code treeModelExploration} / {@code JTree}) */
    private final TreeView<Node> treeExploration = new TreeView<>();
    /** the proof {@link Node}s of the current model to their {@link TreeItem}s */
    private final Map<Node, TreeItem<Node>> nodeToItem = new HashMap<>();
    private final Button jumpToNode = new Button("Jump To Node");
    private final Button pruneExploration = new Button("Prune selected exploration");

    private @Nullable MainWindowF window;
    private @Nullable KeYMediatorF mediator;

    /**
     * the proof shown by this panel; {@code null} empties the panel (Swing {@code currentProof})
     */
    private @Nullable Proof currentProof;
    /** guarded: the model is only collected while the exploration mode is enabled */
    private boolean enabled;
    /** guards the list ↔ tree selection round-trip against mutual recursion */
    private boolean selecting;
    /** the proof root of the current model, for the "Root Node" tree cell */
    private @Nullable Node root;

    /**
     * The rule-application listener (Swing {@code ruleAppListener},
     * ExplorationStepsList.java:47-52): re-collects the steps after every rule application and
     * restores the previously selected tree path. Rule applications may fire from the prover
     * thread, hence the marshalling to the FX thread.
     */
    private final RuleAppListener ruleAppListener = e -> FxUtil.runLater(() -> {
        TreeItem<Node> selected = treeExploration.getSelectionModel().getSelectedItem();
        createModel(e.getSource());
        if (selected != null) {
            TreeItem<Node> item = nodeToItem.get(selected.getValue());
            if (item != null) {
                treeExploration.getSelectionModel().select(item);
            }
        }
    });

    ExplorationStepsPanelF(@Nullable MainWindowF window, @Nullable KeYMediatorF mediator) {
        this.window = window;
        this.mediator = mediator;
        initialize();
    }

    /**
     * (Re-)wires the window/mediator context. The host builds the status bar and the drawer
     * hosts during window construction — before the {@code StartupF#init} hook runs — so the
     * provider calls this from {@code init} to hand the real references to a panel that was
     * already created with {@code null}s.
     */
    void wire(@Nullable MainWindowF window, @Nullable KeYMediatorF mediator) {
        this.window = window;
        this.mediator = mediator;
    }

    /**
     * Sets the shown proof. If {@code null} is given the scenery is emptied otherwise the model
     * reconstructed (Swing {@code ExplorationStepsList.setProof},
     * ExplorationStepsList.java:69-78).
     */
    public void setProof(@Nullable Proof proof) {
        if (currentProof != null) {
            currentProof.removeRuleAppListener(ruleAppListener);
        }
        if (proof != null) {
            proof.addRuleAppListener(ruleAppListener);
        }
        currentProof = proof;
        createModel(proof);
    }

    public void setEnabled(boolean enabled) {
        boolean old = this.enabled;
        this.enabled = enabled;
        if (old != enabled) {
            createModel(currentProof);
        }
    }

    public @Nullable Proof getProof() {
        return currentProof;
    }

    /** @return the status-line indicator label, also shown as part of the panel */
    public Label getHasExplorationSteps() {
        return hasExplorationSteps;
    }

    /** @return the panel title, used as the west-drawer tab title (Swing {@code getTitle}) */
    public String getTitle() {
        return "Exploration Steps";
    }

    private void initialize() {
        // the list and the tree, each with the Swing TitledBorder title as a TitledPane header
        // (ExplorationStepsList.java:209-213)
        listExplorations.setPrefHeight(160);
        listExplorations.setPlaceholder(new Label("No exploration steps."));
        listExplorations.setCellFactory(lv -> new ListCell<>() {
            @Override
            protected void updateItem(Node node, boolean empty) {
                super.updateItem(node, empty);
                if (empty || node == null) {
                    setText(null);
                } else {
                    @Nullable
                    ExplorationNodeData data = node.lookup(ExplorationNodeData.class);
                    setText(data != null && data.getExplorationAction() != null
                            ? node.serialNr() + " " + data.getExplorationAction()
                            : Integer.toString(node.serialNr()));
                }
            }
        });
        TitledPane listPane = new TitledPane("List of Exploration", listExplorations);
        listPane.setCollapsible(false);

        treeExploration.setCellFactory(tv -> new TreeCell<>() {
            @Override
            protected void updateItem(Node node, boolean empty) {
                super.updateItem(node, empty);
                if (empty || node == null) {
                    setText(null);
                    return;
                }
                TreeItem<Node> item = getTreeItem();
                boolean rootCell = item != null && item == treeExploration.getRoot();
                @Nullable
                ExplorationNodeData data = node.lookup(ExplorationNodeData.class);
                String action = data == null ? null : data.getExplorationAction();
                // Swing ExplorationStepsList.MyTreeCellRenderer
                // (ExplorationStepsList.java:306-332); the root cell reuses the "Root Node"
                // label and the (faithfully quirky) serial concatenation of the original.
                if (rootCell) {
                    setText(action != null ? "Root Node" + node.serialNr() + " " + action
                            : "Root Node");
                } else {
                    setText(action != null ? node.serialNr() + " " + action
                            : Integer.toString(node.serialNr()));
                }
            }
        });
        TitledPane treePane = new TitledPane("Explorations in Proof", treeExploration);
        treePane.setCollapsible(false);
        VBox.setVgrow(treePane, Priority.ALWAYS);

        // selection round-trip list ↔ tree and node selection in the mediator
        // (Swing ExplorationStepsList.java:172-202)
        listExplorations.getSelectionModel().selectedItemProperty()
                .addListener((obs, old, value) -> {
                    if (selecting || value == null) {
                        return;
                    }
                    selecting = true;
                    try {
                        TreeItem<Node> item = nodeToItem.get(value);
                        if (item != null) {
                            expandChain(item);
                            treeExploration.getSelectionModel().select(item);
                            treeExploration.scrollTo(
                                treeExploration.getSelectionModel().getSelectedIndex());
                        }
                        if (mediator != null) {
                            mediator.getSelectionModel().setSelectedNode(value);
                        }
                    } finally {
                        selecting = false;
                    }
                });
        treeExploration.getSelectionModel().selectedItemProperty()
                .addListener((obs, old, value) -> {
                    if (selecting || value == null) {
                        return;
                    }
                    selecting = true;
                    try {
                        Node node = value.getValue();
                        if (mediator != null) {
                            mediator.getSelectionModel().setSelectedNode(node);
                        }
                        int selectionIndex = getSelectionIndex(node);
                        if (selectionIndex > -1) {
                            listExplorations.getSelectionModel().select(selectionIndex);
                            listExplorations.scrollTo(selectionIndex);
                        }
                    } finally {
                        selecting = false;
                    }
                });

        // the bottom panel actions (Swing PruneExplorationAction / JumpToNodeAction,
        // ExplorationStepsList.java:357-408): enabled iff an exploration is selected
        jumpToNode.disableProperty()
                .bind(listExplorations.getSelectionModel().selectedItemProperty().isNull());
        pruneExploration.disableProperty()
                .bind(listExplorations.getSelectionModel().selectedItemProperty().isNull());
        jumpToNode.setOnAction(e -> jumpToNode());
        pruneExploration.setOnAction(e -> pruneExploration());
        Tooltip.install(jumpToNode,
            new Tooltip("Jump to the selected exploration node in the proof tree."));
        Tooltip.install(pruneExploration,
            new Tooltip("Prune the proof at the selected exploration node and remove its "
                + "exploration annotation."));
        HBox buttons = new HBox(8, jumpToNode, pruneExploration);
        buttons.setAlignment(Pos.CENTER);

        getChildren().addAll(listPane, treePane, buttons);
        setSpacing(6);
        updateLabel();
    }

    private void jumpToNode() {
        Node selected = listExplorations.getSelectionModel().getSelectedItem();
        if (selected != null && mediator != null) {
            mediator.getSelectionModel().setSelectedNode(selected);
        }
    }

    private void pruneExploration() {
        // Swing ExplorationStepsList.PruneExplorationAction (ExplorationStepsList.java:367-390):
        // prefers the tree selection, falls back to the list selection
        Node explorationNode = null;
        TreeItem<Node> treeSelection = treeExploration.getSelectionModel().getSelectedItem();
        if (treeSelection != null) {
            Node node = treeSelection.getValue();
            pruneTo(node);
            explorationNode = node;
        }
        Node selected = listExplorations.getSelectionModel().getSelectedItem();
        if (selected != null) {
            pruneTo(selected);
            if (explorationNode == null) {
                explorationNode = selected;
            }
        }
        if (explorationNode != null) {
            @Nullable
            ExplorationNodeData data = explorationNode.lookup(ExplorationNodeData.class);
            if (data != null) {
                explorationNode.deregister(data, ExplorationNodeData.class);
            }
            createModel(mediator != null ? mediator.getSelectedProof() : currentProof);
        }
    }

    private void pruneTo(Node node) {
        // KNOWN-SIMPLIFIED: the Swing action prunes via {@code
        // mediator.getUI().getProofControl().pruneTo(...)}; the FX counterpart is the proof
        // control of the window's user-interface control. Headless runs (no window) no-op.
        if (window != null) {
            window.getUserInterfaceControl().getProofControl().pruneTo(node);
        }
    }

    private void createModel(@Nullable Proof model) {
        listModelExploration.clear();
        nodeToItem.clear();
        root = null;
        if (enabled && model != null && !model.isDisposed()) {
            Node proofRoot = model.root();
            root = proofRoot;
            TreeItem<Node> rootItem = new TreeItem<>(proofRoot);
            nodeToItem.put(proofRoot, rootItem);
            treeExploration.setRoot(rootItem);
            List<Node> explorationNodes = collectAllExplorationSteps(proofRoot, rootItem);
            listModelExploration.addAll(explorationNodes);
            setTreeExpandedState(rootItem, true);
        } else {
            treeExploration.setRoot(null);
        }
        updateLabel();
    }

    private void updateLabel() {
        if (listModelExploration.isEmpty()) {
            hasExplorationSteps.setGraphic(noStepsIcon);
            hasExplorationSteps.setTooltip(new Tooltip(
                "The current proof does not contain any exploratory proof steps."));
        } else {
            hasExplorationSteps.setGraphic(hasStepsIcon);
            hasExplorationSteps.setTooltip(new Tooltip(
                "The current proof contains exploratory proof steps."));
        }
    }

    private List<Node> collectAllExplorationSteps(Node proofRoot, TreeItem<Node> rootItem) {
        List<Node> list = new ArrayList<>();
        findExplorationChildren(proofRoot, list, rootItem);
        return list;
    }

    /**
     * Collects the nodes inside the proof tree which carry an exploration annotation, grouping
     * them as a chain in the given tree model during traversal — the faithful port of the Swing
     * {@code findExplorationChildren} depth-first walk (ExplorationStepsList.java:139-166),
     * including the {@code reached} set guarding against revisiting shared subtrees.
     */
    private void findExplorationChildren(Node node, List<Node> foundNodes,
            TreeItem<Node> rootItem) {
        Set<Node> reached = new HashSet<>(512000);
        ArrayDeque<Node> nodes = new ArrayDeque<>(8);
        nodes.add(node);
        TreeItem<Node> parentItem = rootItem;
        while (!nodes.isEmpty()) {
            Node n = nodes.pollLast();
            @Nullable
            ExplorationNodeData data = n.lookup(ExplorationNodeData.class);
            if (data != null && data.getExplorationAction() != null) {
                TreeItem<Node> item = new TreeItem<>(n);
                parentItem.getChildren().add(0, item);
                parentItem = item;
                nodeToItem.putIfAbsent(n, item);
                foundNodes.add(n);
            }
            reached.add(n);
            for (Node child : n) {
                if (!reached.contains(child)) {
                    nodes.push(child);
                }
            }
        }
    }

    /** {@code null}-safe replacement of the Swing cast {@code (MyTreeNode) model.getRoot()} */
    private int getSelectionIndex(Node node) {
        return listModelExploration.indexOf(node);
    }

    private static void setTreeExpandedState(TreeItem<?> item, boolean expanded) {
        item.setExpanded(expanded);
        for (TreeItem<?> child : item.getChildren()) {
            setTreeExpandedState(child, expanded);
        }
    }

    private static void expandChain(TreeItem<?> item) {
        for (TreeItem<?> parent = item.getParent(); parent != null; parent = parent.getParent()) {
            parent.setExpanded(true);
        }
    }
}
