/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;


import java.lang.ref.WeakReference;
import java.util.Enumeration;
import java.util.LinkedList;
import javax.annotation.Nonnull;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;


public abstract class GUIAbstractTreeNode implements TreeNode {

    private final GUIProofTreeModel tree;

    // made weak otherwise there are leaks in ExpansionState.map
    // and ProofTreeView.delegateView.lastPathComponent
    private final WeakReference<Node> noderef;

    protected GUIProofTreeModel getProofTreeModel() {
        return tree;
    }

    public GUIAbstractTreeNode(GUIProofTreeModel tree, Node node) {
        this.tree = tree;
        this.noderef = new WeakReference<>(node);
    }

    public abstract TreeNode getChildAt(int childIndex);

    public abstract int getChildCount();

    public abstract TreeNode getParent();

    public abstract boolean isLeaf();

    public abstract void flushCache();

    public abstract @Nonnull String getSearchString();

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

    protected TreeNode findBranch(Node p_node) {
        TreeNode res = getProofTreeModel().findBranch(p_node);
        if (res != null) {
            return res;
        }

        String label = ensureBranchLabelIsSet(p_node);

        return getProofTreeModel().getBranchNode(p_node, label);
    }

    public static String ensureBranchLabelIsSet(Node p_node) { // TODO: This functionality should be
                                                               // hidden somewhere in NodeInfo
                                                               // without the need to call it
                                                               // explicitly.
        String label = p_node.getNodeInfo().getBranchLabel();

        if (p_node.root()) {
            label = "Proof Tree";
        }
        if (label == null) {
            label = "Case " + (p_node.parent().getChildNr(p_node) + 1);
            p_node.getNodeInfo().setBranchLabel(label);
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

    protected Node findChild(Node n) {
        if (n.childrenCount() == 1) {
            return n.child(0);
        }

        if (!getProofTreeModel().globalFilterActive()) {
            return null;
        }

        Node nextN = null;
        for (int i = 0; i != n.childrenCount(); ++i) {
            if (!ProofTreeViewFilter.hiddenByGlobalFilters(n.child(i))) {
                if (nextN != null) {
                    return null;
                }
                nextN = n.child(i);
            }
        }

        return nextN;
    }
}
