/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.prooftree;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Objects;
import java.util.Set;
import javafx.scene.control.Tooltip;
import javafx.scene.control.TreeCell;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.util.javafx.FxUtil;

/**
 * First JavaFX version of the proof tree view, the counter-part of
 * {@code de.uka.ilkd.key.gui.prooftree.ProofTreeView} (a Swing {@code JTree} driven by
 * {@code GUIProofTreeModel}) in the module {@code key.ui}.
 * <p>
 * <b>Milestone M2, first version.</b> The tree structure is built directly from the
 * {@link Proof}: each branch is rendered as a flat list of rule applications (like the Swing
 * model's linear walk), and at a branch point one sub-branch item per child is created, labeled
 * with the branch label of the child (falling back to {@code Case <n>}, mirroring
 * {@code GUIAbstractTreeNode.ensureBranchLabelIsSet}). Leaves are styled by their goal state
 * (open/closed/interactive). Clicking a node selects it in the {@link KeYSelectionModel};
 * selection changes (and proof changes) drive the view.
 * <p>
 * Deliberately deferred to later M2/M3 chunks: search, filters (ProofTreeViewFilter), heatmap,
 * notes/tooltips of the rich Swing renderer, one-step-simplifier protocol children, lazy
 * population for very large proofs (currently built eagerly), and live updates on rule
 * applications.
 */
public class ProofTreeViewF extends TreeView<ProofTreeViewF.Entry> {

    /**
     * One tree entry: either a proof node entry (a rule application) or a branch entry (labeled
     * sub-tree; {@code node} is the root of the branch).
     */
    public static final class Entry {
        final Node node;
        final String branchLabel;

        private Entry(Node node, String branchLabel) {
            this.node = node;
            this.branchLabel = branchLabel;
        }

        static Entry node(Node node) {
            return new Entry(node, null);
        }

        static Entry branch(Node node, String label) {
            return new Entry(node, Objects.requireNonNull(label));
        }

        public boolean isBranch() {
            return branchLabel != null;
        }

        public Node node() {
            return node;
        }

        /**
         * @return the text shown for this entry, whitespace-normalized like the Swing renderer
         */
        public String displayText() {
            if (branchLabel != null) {
                return branchLabel;
            }
            String text = node.serialNr() + ":" + node.name();
            return text.replaceAll("\\s+", " ");
        }
    }

    private KeYSelectionModel selectionModel;
    private Proof proof;
    private boolean updatingSelection;

    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        @Override
        public void selectedNodeChanged(KeYSelectionEvent<Node> event) {
            revealSelectedNode();
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
            setProof(event.getSource().getSelectedProof());
        }
    };

    /**
     * Creates an empty proof tree view.
     */
    public ProofTreeViewF() {
        getStyleClass().add("proof-tree");
        setCellFactory(view -> new ProofTreeCell());
        getSelectionModel().selectedItemProperty()
                .addListener((obs, oldItem, newItem) -> handleTreeSelection(newItem));
    }

    /**
     * Registers this view as a selection listener on the given model and shows the currently
     * selected proof, if any.
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
        revealSelectedNode();
    }

    /**
     * Shows the given proof, replacing any previously shown tree.
     *
     * @param newProof the proof to display, may be {@code null}
     */
    public void setProof(Proof newProof) {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(() -> setProof(newProof));
            return;
        }
        proof = newProof;
        updatingSelection = true;
        try {
            if (proof == null) {
                setRoot(null);
            } else {
                TreeItem<Entry> root = buildBranch(proof.root(), "Proof Tree");
                setRoot(root);
                root.setExpanded(true);
            }
        } finally {
            updatingSelection = false;
        }
    }

    /**
     * Rebuilds the tree from the current proof (used when rule applications changed it).
     */
    public void refresh() {
        setProof(proof);
    }

    /**
     * Development self-test (M2): verifies that every proof node appears exactly once as a node
     * entry (each node is either on a branch's linear chain or the root of exactly one branch,
     * whose folder is an additional labeled entry like the Swing model's branch nodes).
     *
     * @return a one-line report, {@code "... PASS"} if the structure is consistent
     */
    public String verifyTreeStructure() {
        if (proof == null || getRoot() == null) {
            return "no proof";
        }
        Set<Node> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        int[] counters = { 0, 0 }; // node entries, branch entries
        collect(getRoot(), seen, counters);
        int proofNodeCount = 0;
        for (Iterator<Node> it = proof.root().subtreeIterator(); it.hasNext();) {
            it.next();
            proofNodeCount++;
        }
        boolean pass = seen.size() == proofNodeCount && counters[0] == proofNodeCount;
        return "proofNodes=" + proofNodeCount + " nodeEntries=" + counters[0] + " unique="
            + seen.size() + " branches=" + counters[1] + " " + (pass ? "PASS" : "FAIL");
    }

    private static void collect(TreeItem<Entry> item, Set<Node> seen, int[] counters) {
        Entry entry = item.getValue();
        if (entry != null && entry.node != null) {
            seen.add(entry.node);
            if (entry.isBranch()) {
                counters[1]++;
            } else {
                counters[0]++;
            }
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            collect(child, seen, counters);
        }
    }

    private TreeItem<Entry> buildBranch(Node branchRoot, String label) {
        TreeItem<Entry> branchItem = new TreeItem<>(Entry.branch(branchRoot, label));

        Node current = branchRoot;
        // linear walk along single-child nodes, mirroring GUIBranchNode.fillChildrenCache
        while (true) {
            TreeItem<Entry> item = new TreeItem<>(Entry.node(current));
            branchItem.getChildren().add(item);
            if (current.childrenCount() == 1) {
                current = current.child(0);
                continue;
            }
            break;
        }
        // at a branch point (or a leaf): one branch item per child
        for (Node child : current.children()) {
            branchItem.getChildren().add(buildBranch(child, ensureBranchLabelIsSet(child)));
        }
        return branchItem;
    }

    /**
     * Returns the branch label of the given node, falling back to {@code Case <n>} and storing it
     * on the node like {@code GUIAbstractTreeNode.ensureBranchLabelIsSet}.
     */
    private static String ensureBranchLabelIsSet(Node node) {
        var nodeInfo = node.getNodeInfo();
        String label;
        if (node.root()) {
            label = "Proof Tree";
        } else {
            synchronized (nodeInfo) {
                label = nodeInfo.getBranchLabel();
                if (label == null) {
                    label = "Case " + (node.parent().getChildNr(node) + 1);
                    nodeInfo.setBranchLabel(label);
                }
            }
        }
        return label;
    }

    private void handleTreeSelection(TreeItem<Entry> item) {
        if (updatingSelection || item == null || item.getValue() == null) {
            return;
        }
        Node node = item.getValue().node();
        if (node != null && selectionModel != null && node != selectionModel.getSelectedNode()) {
            selectionModel.setSelectedNode(node);
        }
    }

    /**
     * Selects and reveals the tree item of the currently selected node, if present.
     */
    private void revealSelectedNode() {
        Node selected = selectionModel != null ? selectionModel.getSelectedNode() : null;
        if (selected == null || getRoot() == null) {
            return;
        }
        TreeItem<Entry> item = findItem(getRoot(), selected);
        if (item == null || getSelectionModel().getSelectedItem() == item) {
            return;
        }
        updatingSelection = true;
        try {
            // expand the ancestors so the item is visible
            TreeItem<Entry> a = item.getParent();
            while (a != null) {
                a.setExpanded(true);
                a = a.getParent();
            }
            getSelectionModel().select(item);
            scrollTo(getRow(item));
        } finally {
            updatingSelection = false;
        }
    }

    private static TreeItem<Entry> findItem(TreeItem<Entry> start, Node node) {
        if (start.getValue() != null && start.getValue().node() == node) {
            return start;
        }
        for (TreeItem<Entry> child : start.getChildren()) {
            TreeItem<Entry> result = findItem(child, node);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    /**
     * The tree cell rendering: text plus the goal-state style class (Swing colors map onto the
     * theme's CSS properties).
     */
    private final class ProofTreeCell extends TreeCell<Entry> {
        @Override
        protected void updateItem(Entry item, boolean empty) {
            super.updateItem(item, empty);
            if (empty || item == null) {
                setText(null);
                setTooltip(null);
                getStyleClass().clear();
                getStyleClass().add("proof-tree-cell");
                return;
            }
            setText(item.displayText());
            getStyleClass().clear();
            getStyleClass().add("proof-tree-cell");
            getStyleClass().add(styleClassOf(item));
            setTooltip(new Tooltip(tooltipText(item)));
        }

        private String styleClassOf(Entry item) {
            Node node = item.node;
            if (item.isBranch()) {
                return node.isClosed() ? "proof-tree-branch-closed" : "proof-tree-branch";
            }
            if (node.leaf()) {
                if (node.isClosed()) {
                    return "proof-tree-closed";
                }
                Goal goal = proof != null ? proof.getOpenGoal(node) : null;
                if (goal == null) {
                    return "proof-tree-closed";
                }
                return goal.isAutomatic() ? "proof-tree-open" : "proof-tree-interactive";
            }
            return "proof-tree-inner";
        }

        private String tooltipText(Entry item) {
            if (item.isBranch()) {
                return "Branch: " + item.branchLabel;
            }
            return "Node " + item.node.serialNr();
        }
    }
}
