/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.prooftree;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.List;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public abstract class GUIAbstractTreeNode implements TreeNode {

    private final GUIProofTreeModel tree;

    // made weak otherwise there are leaks in ExpansionState.map
    // and ProofTreeView.delegateView.lastPathComponent
    private final WeakReference<Node> noderef;

    protected @Nullable TreeNode parent;

    protected GUIProofTreeModel getProofTreeModel() {
        return tree;
    }

    protected GUIAbstractTreeNode(GUIProofTreeModel tree, Node node) {
        this.tree = tree;
        this.noderef = new WeakReference<>(node);
    }

    public abstract TreeNode getChildAt(int childIndex);

    public abstract int getChildCount();

    /**
     * Returns the parent of this node.
     *
     * <p>
     * The JDK declares a non-null return, although the proof-tree root node has no parent and
     * reports {@code null} (as does a node whose wrapped proof node was collected), which the
     * swing tree tolerates as the end of the path; both cases are deliberate and suppressed
     * with a scoped key.
     */
    @SuppressWarnings("nullness:return.type.incompatible")
    @Override
    public TreeNode getParent() {
        Node node = getNode();
        if (parent == null && this != tree.getRoot()
                && !(node != null && ProofTreeViewFilter.hiddenByGlobalFilters(node))) {
            if (node != null && node.proof().root() == node) {
                return (TreeNode) null; // TODO: why can there be another instance of the root node?
            }
            throw new IllegalStateException("abstract tree node without parent: " + this);
        }
        TreeNode parentNode = parent;
        return parentNode == null ? (TreeNode) null : parentNode;
    }

    public abstract boolean isLeaf();

    public abstract void flushCache();

    public abstract @NonNull String getSearchString();

    public int getIndex(TreeNode node) {
        for (int i = 0; i < getChildCount(); i++) {
            if (getChildAt(i).equals(node)) {
                return i;
            }
        }
        return -1;
    }

    public boolean getAllowsChildren() {
        return !isLeaf();
    }

    public Enumeration<TreeNode> children() {
        return new ChildEnumeration();
    }

    public TreeNode[] getPath() {
        LinkedList<TreeNode> path = new LinkedList<>();
        TreeNode n = this;
        path.addFirst(n);
        while ((n = n.getParent()) != null) {
            path.addFirst(n);
        }
        return path.toArray(new TreeNode[0]);
    }

    protected GUIAbstractTreeNode findBranch(Node p_node) {
        GUIAbstractTreeNode res = getProofTreeModel().findBranch(p_node);
        if (res != null) {
            return res;
        }

        String label = ensureBranchLabelIsSet(p_node);

        return getProofTreeModel().getBranchNode(p_node, label);
    }

    public static String ensureBranchLabelIsSet(Node p_node) { // TODO: This functionality should be
        // hidden somewhere in NodeInfo
        // without the need to call it explicitly.
        var nodeInfo = p_node.getNodeInfo();
        String label;
        if (p_node.root()) {
            label = "Proof Tree";
        } else {
            synchronized (nodeInfo) {
                label = nodeInfo.getBranchLabel();
                if (label == null) {
                    Node parentNode = p_node.parent();
                    if (parentNode == null) {
                        // a non-root proof node always has a parent
                        throw new NullPointerException("No parent proof node available.");
                    }
                    label = "Case " + (parentNode.getChildNr(p_node) + 1);
                    nodeInfo.setBranchLabel(label);
                }
            }
        }
        return label;
    }

    private class ChildEnumeration implements Enumeration<TreeNode> {
        int current = 0;

        public boolean hasMoreElements() {
            return current < getChildCount();
        }

        public TreeNode nextElement() {
            return getChildAt(current++);
        }

    }

    public @Nullable Node getNode() {
        return noderef.get();
    }

    /**
     * Get the children of the specified node whilst respecting the configured
     * global view filters.
     *
     * @param n the nodes
     * @return children nodes
     */
    protected List<Node> findChild(Node n) {
        if (n.childrenCount() == 1) {
            return List.of(n.child(0));
        }

        if (!getProofTreeModel().globalFilterActive()
                && !getProofTreeModel().linearizedModeActive()) {
            return List.of();
        }

        List<Node> nextN = new ArrayList<>();
        for (int i = 0; i != n.childrenCount(); ++i) {
            if (!ProofTreeViewFilter.hiddenByGlobalFilters(n.child(i))) {
                nextN.add(n.child(i));
            }
        }

        return nextN;
    }

    protected void setParent(TreeNode parent) {
        this.parent = parent;
    }
}
