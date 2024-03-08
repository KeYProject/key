/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.util.ArrayList;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;

import org.jspecify.annotations.NonNull;

/**
 * this class implements a TreeModel that can be displayed using the JTree class framework
 */
class GUIBranchNode extends GUIAbstractTreeNode implements TreeNode {

    private final Object label;

    private ArrayList<TreeNode> childrenCache = null;


    public GUIBranchNode(GUIProofTreeModel tree, Node subTree, Object label) {
        super(tree, subTree);
        this.label = label;
    }

    @Override
    public TreeNode getChildAt(int childIndex) {
        ensureChildrenCacheExists();
        return childrenCache.get(childIndex);
    }

    private void ensureChildrenCacheExists() {
        if (childrenCache == null) {
            childrenCache = new ArrayList<>();
        } else {
            return;
        }

        Node n = getNode();

        if (n == null) {
            return;
        }

        while (true) {
            childrenCache.add(getProofTreeModel().getProofTreeNode(n));
            Node nextN = findChild(n);
            // skip nodes that are hidden in the proof tree
            while (nextN != null && nextN.isHideInProofTree()) {
                nextN = findChild(nextN);
            }
            if (nextN == null) {
                break;
            }
            n = nextN;
        }

        for (int i = 0; i != n.childrenCount(); ++i) {
            if (!ProofTreeViewFilter.hiddenByGlobalFilters(n.child(i))
                    && !n.child(i).isHideInProofTree()) {
                childrenCache.add(findBranch(n.child(i)));
            }
        }
    }

    @Override
    public void flushCache() {
        childrenCache = null;
    }

    @NonNull
    @Override
    public String getSearchString() {
        return toString();
    }

    public int getChildCount() {
        if (childrenCache == null) {
            ensureChildrenCacheExists();
        }
        return childrenCache.size();
    }


    public TreeNode getParent() {
        Node self = getNode();
        if (self == null) {
            return null;
        }
        Node n = self.parent();
        if (n == null) {
            return null;
        } else {
            while (n.parent() != null && findChild(n.parent()) != null) {
                n = n.parent();
            }
            return findBranch(n);
        }
    }

    // signalled by GUIProofTreeModel when the user has altered the value
    public void setLabel(String s) {
        Node n = getNode();
        if (n != null) {
            n.getNodeInfo().setBranchLabel(s);
        }
    }

    public boolean isLeaf() {
        return false;
    }

    public String toString() {
        Node n = getNode();
        String res;
        if (n != null) {
            res = n.getNodeInfo().getBranchLabel();
            if (res == null) {
                return label.toString();
            }
        } else {
            res = "null";
        }
        return res;
    }

    public boolean isClosed() {
        Node node = getNode();
        return node != null && node.isClosed();
    }
}
