/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.Taclet;

import org.jspecify.annotations.NonNull;

/**
 * Branch node indicating the start of a new proof branch.
 *
 * @author early KeY team
 * @see ProofTreeView
 */
class GUIBranchNode extends GUIAbstractTreeNode {

    private final Object label;

    private ArrayList<TreeNode> childrenCache = null;


    public GUIBranchNode(GUIProofTreeModel tree, Node subTree, Object label) {
        super(tree, subTree);
        this.label = label;
    }

    private void createChildrenCache() {
        childrenCache = new ArrayList<>();
    }

    public TreeNode getChildAt(int childIndex) {
        fillChildrenCache(false);
        return childrenCache.get(childIndex);
    }

    /**
     * Fill the {@link #childrenCache}.
     *
     * @param dryRun if true, only count the number of children that would be added
     * @return number of children
     */
    private int fillChildrenCache(boolean dryRun) {
        if (childrenCache == null && !dryRun) {
            createChildrenCache();
        }

        if (childrenCache != null && !childrenCache.isEmpty()) {
            return childrenCache.size();
        }

        int count = 0;
        Node n = getNode();

        if (n == null) {
            return 0;
        }

        while (true) {
            // While searching, hide intermediate proof steps that do not match the query
            // (the subtree is still shown because it contains a match somewhere); this
            // collapses the branch down to the matching steps. Branch nodes added below are
            // always kept, as they are filtered by the global "contains match" check.
            if (showStep(n)) {
                count++;
                if (!dryRun) {
                    var newNode = getProofTreeModel().getProofTreeNode(n);
                    newNode.setParent(this);
                    childrenCache.add(newNode);
                }
            }
            List<Node> nextN = findChild(n);
            if (nextN.isEmpty()) {
                break;
            }
            if (nextN.size() > 1) {
                // linearized mode: the main branch will be continued without a new BranchNode
                if (getProofTreeModel().linearizedModeActive()
                        && (n.getAppliedRuleApp().rule() instanceof Taclet taclet && Objects
                                .equals(taclet.goalTemplates().last().tag(), "main"))) {
                    n = nextN.get(0);
                    nextN.remove(0);
                    for (var node : nextN) {
                        count++;
                        if (!dryRun) {
                            var branchNode = findBranch(node);
                            branchNode.setParent(this);
                            childrenCache.add(branchNode);
                        }
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
                count++;
                if (!dryRun) {
                    var branchNode = findBranch(n.child(i));
                    branchNode.setParent(this);
                    childrenCache.add(branchNode);
                }
            }
        }
        return count;
    }

    /**
     * @param n a proof node on this branch's linear chain.
     * @return whether the corresponding proof step should be shown. While the collapsing search
     *         is active, only steps matching the query are shown; otherwise all steps are shown.
     */
    private static boolean showStep(Node n) {
        return !ProofTreeViewFilter.SEARCH.isActive() || ProofTreeViewFilter.SEARCH.matches(n);
    }

    @Override
    public void flushCache() {
        childrenCache = null;
    }

    @Override
    public @NonNull String getSearchString() {
        return toString();
    }

    @Override
    public int getChildCount() {
        return fillChildrenCache(true);
    }

    /**
     * Set the label of this branch node.
     * Signalled by GUIProofTreeModel when the user has altered the value.
     *
     * @param s new label
     */
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

    @Override
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

    /**
     * @return whether this branch is closed
     * @see Node#isClosed()
     */
    public boolean isClosed() {
        Node node = getNode();
        return node != null && node.isClosed();
    }
}
