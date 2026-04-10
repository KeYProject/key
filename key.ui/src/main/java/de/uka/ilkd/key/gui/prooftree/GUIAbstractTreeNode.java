/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;


import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.List;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;

import org.jspecify.annotations.NonNull;

public abstract class GUIAbstractTreeNode implements TreeNode {

    private final GUIProofTreeModel tree;

    // made weak otherwise there are leaks in ExpansionState.map
    // and ProofTreeView.delegateView.lastPathComponent
    private final WeakReference<Node> noderef;

    protected TreeNode parent;

    protected GUIProofTreeModel getProofTreeModel() {
        return tree;
    }

    protected GUIAbstractTreeNode(GUIProofTreeModel tree, Node node) {
        this.tree = tree;
        this.noderef = new WeakReference<>(node);
    }

    public abstract TreeNode getChildAt(int childIndex);

    public abstract int getChildCount();

    @Override
    public TreeNode getParent() {
        if (parent == null && this != tree.getRoot()
                && !(getNode() != null && ProofTreeViewFilter.hiddenByGlobalFilters(getNode()))) {
            Node n = getNode();
            if (n != null && n.proof().root() == n) {
                return null; // TODO: why can there be another instance of the root node?
            }
            throw new IllegalStateException("abstract tree node without parent: " + this);
        }
        return parent;
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
                    label = "Case " + (p_node.parent().getChildNr(p_node) + 1);
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

    public Node getNode() {
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
