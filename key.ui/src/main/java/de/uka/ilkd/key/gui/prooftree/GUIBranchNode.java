/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.util.List;
import javax.annotation.Nonnull;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;

/**
 * Branch node indicating the start of a new proof branch.
 *
 * @see ProofTreeView
 */
class GUIBranchNode extends GUIAbstractTreeNode implements TreeNode {
    private static final String NORM = "Normal Execution";

    private final Object label;

    public GUIBranchNode(GUIProofTreeModel tree, Node subTree, Object label) {
        super(tree, subTree);
        this.label = label;
    }


    private GUIAbstractTreeNode[] childrenCache = null;

    private void createChildrenCache() {
        childrenCache = new GUIAbstractTreeNode[getChildCountHelp()];
    }

    public TreeNode getChildAt(int childIndex) {
        fillChildrenCache();
        return childrenCache[childIndex];
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
            childrenCache[count].setParent(this);
            count++;
            List<Node> nextN = findChild(n);
            if (nextN.isEmpty()) {
                break;
            }
            if (nextN.size() > 1) {
                if (nextN.get(0).getNodeInfo().getBranchLabel() != null
                        && nextN.get(0).getNodeInfo().getBranchLabel().startsWith(NORM)) {
                    n = nextN.get(0);
                    nextN.remove(0);
                    for (var node : nextN) {
                        childrenCache[count] = findBranch(node);
                        childrenCache[count].setParent(this);
                        count++;
                    }
                    continue;
                } else {
                    break;
                }
            }
            n = nextN.get(0);
        }

        for (int i = 0; i != n.childrenCount(); ++i) {
            if (!ProofTreeViewFilter.hiddenByGlobalFilters(n.child(i))) {
                childrenCache[count] = findBranch(n.child(i));
                childrenCache[count].setParent(this);
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
            List<Node> nextN = findChild(n);
            if (nextN.isEmpty()) {
                break;
            }
            if (nextN.size() > 1) {
                if (nextN.get(0).getNodeInfo().getBranchLabel() != null
                        && nextN.get(0).getNodeInfo().getBranchLabel().startsWith(NORM)) {
                    n = nextN.get(0);
                    count += nextN.size() - 1;
                    continue;
                } else {
                    break;
                }
            }
            n = nextN.get(0);
        }

        for (int i = 0; i != n.childrenCount(); ++i) {
            if (!ProofTreeViewFilter.hiddenByGlobalFilters(n.child(i))) {
                count++;
            }
        }

        return count;
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
