/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.util.Arrays;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Filters for the proof tree view.
 *
 * @author bruns
 * @author lanzinger
 */
public abstract class ProofTreeViewFilter {

    /**
     * Hide Intermediate Proofsteps
     */
    public final static ProofTreeViewFilter HIDE_INTERMEDIATE = new HideIntermediateFilter();

    /**
     * Hide Closed Subtrees
     */
    public final static ProofTreeViewFilter HIDE_CLOSED_SUBTREES = new HideClosedSubtreesFilter();

    /**
     * Hide Non-interactive Proofsteps.
     */
    public final static ProofTreeViewFilter ONLY_INTERACTIVE = new OnlyInteractiveFilter();

    /**
     * Hide Subtrees Whose Goals are Interactive.
     */
    public final static ProofTreeViewFilter HIDE_INTERACTIVE_GOALS =
        new HideInteractiveGoalsFilter();

    /**
     * All ProofTreeViewFilters.
     */
    public final static ProofTreeViewFilter[] ALL = new ProofTreeViewFilter[] { HIDE_INTERMEDIATE,
        ONLY_INTERACTIVE, HIDE_CLOSED_SUBTREES, HIDE_INTERACTIVE_GOALS };

    /**
     * All ProofTreeViewFilters that operate on whole subtrees, as opposed to {@link NodeFilter}s,
     * which operate on single nodes.
     */
    public final static ProofTreeViewFilter[] ALL_GLOBAL_FILTERS =
        new ProofTreeViewFilter[] { HIDE_CLOSED_SUBTREES, HIDE_INTERACTIVE_GOALS };

    /**
     *
     * @param node a node.
     * @return {@code true} iff the subtree starting at {@code node} is hidden by an active global
     *         filter.
     */
    public static boolean hiddenByGlobalFilters(Node node) {
        return Arrays.stream(ALL_GLOBAL_FILTERS)
                .anyMatch(filter -> filter.isActive() && !filter.showSubtree(node));
    }

    /**
     * @return the name of the filter used in GUI elements.
     */
    public abstract String name();

    /**
     *
     * @param node a node.
     * @return {@code false} iff the subtree starting at {@code node} is hidden by this filter.
     */
    public abstract boolean showSubtree(Node node);

    /**
     * @return whether the filter is currently active.
     */
    public abstract boolean isActive();

    /**
     * @return whether this filter should be added to the {@link ProofTreeView}
     */
    public boolean addToProofTreeView() {
        return true;
    }

    /**
     * Should only be called through GUIProofTreeNode#setFilter().
     *
     * @param active whether the filter should be activated or deactivated.
     */
    abstract void setActive(boolean active);

    /**
     * @return whether the filter's scope is on the whole tree (like hiding subtrees).
     */
    abstract boolean global();

    /**
     * Filters working locally on nodes. There may only be one such filter active at any time.
     *
     * @author bruns
     */
    abstract static class NodeFilter extends ProofTreeViewFilter {
        @Override
        boolean global() {
            return false;
        }

        /**
         * Decides whether a child should be counted while iterating all children. A child should
         * not be counted if it is hidden by one of the active filters.
         *
         * @param child a node.
         * @param parent the node's parent.
         * @param pos the node's index in the parent's children array (see
         *        {@link TreeNode#getChildAt(int)}.
         */
        protected abstract boolean countChild(GUIProofTreeNode child, TreeNode parent, int pos);

        /**
         *
         * @param parent a node.
         * @return the number of child nodes, not counting the ones hidden by the active filters.
         * @see #countChild(TreeNode, TreeNode, int)
         */
        public int getChildCount(Object parent) {
            TreeNode child;
            int count = 0;
            for (int i = 0; i < ((TreeNode) parent).getChildCount(); i++) {
                child = ((TreeNode) parent).getChildAt(i);
                if (countChild(child, (TreeNode) parent, i)) {
                    count++;
                }
            }
            return count;
        }

        /**
         *
         * @param parent a node.
         * @param index an index.
         * @return the node's {@code index}th child, not counting the ones hidden by the active
         *         filters.
         * @see #countChild(TreeNode, TreeNode, int)
         */
        public Object getChild(Object parent, int index) {
            TreeNode child;
            int count = -1;
            for (int i = 0; i < ((TreeNode) parent).getChildCount(); i++) {
                child = ((TreeNode) parent).getChildAt(i);
                if (countChild(child, (TreeNode) parent, i)) {
                    count++;
                    if (index == count) {
                        return child;
                    }
                }
            }
            return null;
        }

        /**
         *
         * @param parent a parent node.
         * @param child a child node.
         * @return the child's index after applying all active filters to the children, or
         *         {@code -1} if {@code child} is not a child of {@code parent}.
         */
        public int getIndexOfChild(Object parent, Object child) {
            TreeNode guiParent = (TreeNode) parent;
            int count = -1;
            for (int i = 0; i < guiParent.getChildCount(); i++) {
                if (countChild(guiParent.getChildAt(i), guiParent, i)) {
                    count++;
                    if (guiParent.getChildAt(i) == child) {
                        return count;
                    }
                }
            }
            return -1;
        }


        /**
         * Decides whether a child should be counted while iterating all children. A child should
         * not be counted if it is hidden by one of the active filters.
         *
         * @param child a node.
         * @param parent the node's parent.
         * @param pos the node's index in the parent's children array (see
         *        {@link TreeNode#getChildAt(int)}.
         */
        protected boolean countChild(TreeNode child, TreeNode parent, int pos) {
            if (child instanceof GUIProofTreeNode) {
                return countChild((GUIProofTreeNode) child, parent, pos);
            } else if (child instanceof GUIBranchNode) {
                return true;
            }
            return true;
        }
    }

    private static class HideIntermediateFilter extends NodeFilter {

        @Override
        protected boolean countChild(GUIProofTreeNode node, TreeNode parent, int pos) {
            if (pos == parent.getChildCount() - 1) {
                return true;
            }

            // count if child is inlined because of a hidden subtree
            for (ProofTreeViewFilter filter : ProofTreeViewFilter.ALL_GLOBAL_FILTERS) {
                if (filter.isActive() && !(parent.getChildAt(pos + 1) instanceof GUIBranchNode)
                        && node.getNode().childrenCount() != 1) {
                    return true;
                }
            }

            return false;
        }

        @Override
        public boolean isActive() {
            return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .getHideIntermediateProofsteps();
        }

        @Override
        void setActive(boolean active) {
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .setHideIntermediateProofsteps(active);
        }

        @Override
        public String name() {
            return "Hide Intermediate Proofsteps";
        }

        @Override
        public boolean showSubtree(Node node) {
            Node parent = node.parent();
            return node.equals(parent.child(parent.childrenCount() - 1));
        }
    }

    private static class OnlyInteractiveFilter extends NodeFilter {

        @Override
        protected boolean countChild(GUIProofTreeNode node, TreeNode parent, int pos) {
            if (node.getNode().getNodeInfo().getInteractiveRuleApplication()) {
                return true;
            }

            if (pos == parent.getChildCount() - 1) {
                return true;
            }

            // count if child is inlined because of a hidden subtree
            for (ProofTreeViewFilter filter : ProofTreeViewFilter.ALL_GLOBAL_FILTERS) {
                if (filter.isActive() && !(parent.getChildAt(pos + 1) instanceof GUIBranchNode)
                        && node.getNode().childrenCount() != 1) {
                    return true;
                }
            }

            return false;
        }

        @Override
        public boolean isActive() {
            return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .getHideAutomodeProofsteps();
        }

        @Override
        void setActive(boolean active) {
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .setHideAutomodeProofsteps(active);
        }

        @Override
        public String name() {
            return "Hide Non-interactive Proofsteps";
        }

        @Override
        public boolean showSubtree(Node node) {
            return node.getNodeInfo().getInteractiveRuleApplication();
        }
    }

    private static class HideClosedSubtreesFilter extends ProofTreeViewFilter {

        @Override
        public boolean isActive() {
            return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .getHideClosedSubtrees();
        }

        @Override
        void setActive(boolean active) {
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .setHideClosedSubtrees(active);
        }

        @Override
        public String name() {
            return "Hide Closed Subtrees";
        }

        @Override
        boolean global() {
            return true;
        }

        @Override
        public boolean showSubtree(Node node) {
            return !node.isClosed();
        }
    }

    private static class HideInteractiveGoalsFilter extends ProofTreeViewFilter {

        @Override
        public boolean isActive() {
            return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .getHideInteractiveGoals();
        }

        @Override
        void setActive(boolean active) {
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .setHideInteractiveGoals(active);
        }

        @Override
        public String name() {
            return "Hide Subtrees Whose Goals are Interactive";
        }

        @Override
        boolean global() {
            return true;
        }

        @Override
        public boolean addToProofTreeView() {
            return false;
        }

        @Override
        public boolean showSubtree(Node node) {
            Proof proof = node.proof();

            // Show subtrees with at least one automatic goal.
            for (Goal goal : proof.getSubtreeGoals(node)) {
                if (goal.isAutomatic()) {
                    return true;
                }
            }

            // Also show closed subtrees.
            return proof.getSubtreeGoals(node).isEmpty();
        }
    }
}
