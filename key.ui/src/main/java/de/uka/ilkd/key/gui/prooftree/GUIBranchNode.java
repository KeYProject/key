/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;
/**
 * this class implements a TreeModel that can be displayed using the JTree class framework
 */

import javax.annotation.Nonnull;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;

class GUIBranchNode extends GUIAbstractTreeNode implements TreeNode {

    private final Object label;

    public GUIBranchNode(GUIProofTreeModel tree, Node subTree, Object label) {
        super(tree, subTree);
        this.label = label;
    }


    private TreeNode[] childrenCache = null;

    private void createChildrenCache() {
        childrenCache = new TreeNode[getChildCountHelp()];
    }

    public TreeNode getChildAt(int childIndex) {
        fillChildrenCache();
        return childrenCache[childIndex];

        /*
         * int count = 0; Node n = subTree; while ( childIndex != count && n.childrenCount() == 1 )
         * { count++; n = n.child(0); } if ( childIndex == count ) { return getProofTreeModel
         * ().getProofTreeNode(n); } else { return findBranch ( n.child(childIndex-count-1) ); }
         */
    }

    private void fillChildrenCache() {
        if (childrenCache == null) {
            createChildrenCache();
        }

        if (childrenCache.length == 0 || childrenCache[0] != null) {
            return;
        }

        int count = 0;
        Node n = getNode();

        if (n == null) {
            return;
        }

        while (true) {
            childrenCache[count] = getProofTreeModel().getProofTreeNode(n);
            count++;
            final Node nextN = findChild(n);
            if (nextN == null) {
                break;
            }
            n = nextN;
        }

        for (int i = 0; i != n.childrenCount(); ++i) {
            if (!ProofTreeViewFilter.hiddenByGlobalFilters(n.child(i))) {
                childrenCache[count] = findBranch(n.child(i));
                count++;
            }
        }
    }

    @Override
    public void flushCache() {
        childrenCache = null;
    }

    @Nonnull
    @Override
    public String getSearchString() {
        return toString();
    }

    public int getChildCount() {
        if (childrenCache == null) {
            createChildrenCache();
        }
        return childrenCache.length;
    }

    private int getChildCountHelp() {
        int count = 0;
        Node n = getNode();

        if (n == null) {
            return 0;
        }

        while (true) {
            count++;
            final Node nextN = findChild(n);
            if (nextN == null) {
                break;
            }
            n = nextN;
        }

        for (int i = 0; i != n.childrenCount(); ++i) {
            if (!ProofTreeViewFilter.hiddenByGlobalFilters(n.child(i))) {
                count++;
            }
        }

        return count;
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
