/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.util.List;
import java.util.Objects;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.Taclet;

import org.jspecify.annotations.NonNull;

/**
 * Branch node indicating the start of a new proof branch.
 *
 * @see ProofTreeView
 */
class GUIBranchNode extends GUIAbstractTreeNode implements TreeNode {
    private static final String MAIN_LABEL = "Normal Execution";

    private final Object label;

    public GUIBranchNode(GUIProofTreeModel tree, Node subTree, Object label) {
        super(tree, subTree);
        this.label = label;
    }


    private GUIAbstractTreeNode[] childrenCache = null;

    private void createChildrenCache() {
        childrenCache = new GUIAbstractTreeNode[getChildCountHelp()];
    }

    @Override
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
                // linearized mode: the main branch will be continued without a new BranchNode
                if (getProofTreeModel().linearizedModeActive()
                        && (nextN.get(0).getNodeInfo().getBranchLabel() != null
                                && nextN.get(0).getNodeInfo().getBranchLabel()
                                        .startsWith(MAIN_LABEL)
                                || n.getAppliedRuleApp().rule() instanceof Taclet taclet && Objects
                                        .equals(taclet.goalTemplates().last().getTag(), "main"))) {
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

    @NonNull
    @Override
    public String getSearchString() {
        return toString();
    }

    @Override
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
                if (getProofTreeModel().linearizedModeActive()
                        && (nextN.get(0).getNodeInfo().getBranchLabel() != null
                                && nextN.get(0).getNodeInfo().getBranchLabel()
                                        .startsWith(MAIN_LABEL)
                                || n.getAppliedRuleApp().rule() instanceof Taclet taclet && Objects
                                        .equals(taclet.goalTemplates().last().getTag(), "main"))) {
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

    @Override
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
