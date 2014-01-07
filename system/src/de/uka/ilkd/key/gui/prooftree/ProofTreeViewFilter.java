package de.uka.ilkd.key.gui.prooftree;

import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;

/**
 * Filters for the proof tree view.
 * @author bruns
 *
 */
public abstract class ProofTreeViewFilter {

	public final static ProofTreeViewFilter HIDE_INTERMEDIATE = new HideIntermediateFilter();
	public final static ProofTreeViewFilter HIDE_CLOSED_SUBTREES = new HideClosedSubtreesFilter();
	public final static ProofTreeViewFilter ONLY_INTERACTIVE = new OnlyInteractiveFilter();

	public final static ProofTreeViewFilter[] ALL =
		new ProofTreeViewFilter[] {HIDE_INTERMEDIATE, ONLY_INTERACTIVE, HIDE_CLOSED_SUBTREES};

	/**
	 * Name of the filter used in GUI elements.
	 */
	public abstract String name();

	/**
	 * Whether the filter is currently active.
	 */
	public abstract boolean isActive ();

	/**
	 * Should only be called through GUIProofTreeNode#setFilter().
	 */
	abstract void setActive(boolean active);

	/**
	 * Returns whether the filter's scope is on the whole tree (like hiding subtrees).
	 */
	abstract boolean global();

	/**
	 * Filters working locally on nodes.
	 * There may only be one such filter active at any time.
	 * @author bruns
	 */
	abstract static class NodeFilter extends ProofTreeViewFilter {
	    @Override
	    boolean global() {
	        return false;
	    }

	    public abstract boolean countChild(GUIProofTreeNode child, TreeNode parent);

	    public int getChildCount(Object parent) {
	        TreeNode child;
	        int count = 0;
	        for (int i = 0; i < ((TreeNode) parent).getChildCount(); i++) {
	            child = ((TreeNode) parent).getChildAt(i);
	            if (countChild(child, (TreeNode) parent)) {
	                count++;
	            }
	        }
	        return count;
	    }

	    public Object getChild(Object parent, int index) {
	        TreeNode child;
	        int count = -1;
	        for (int i = 0; i < ((TreeNode) parent).getChildCount(); i++) {
	            child = ((TreeNode) parent).getChildAt(i);
	            if (countChild(child, (TreeNode) parent)) {
	                count++;
	                if (index == count) {
	                    return child;
	                }
	            }
	        }
	        return null;
	    }


	    public int getIndexOfChild(Object parent, Object child) {
	        TreeNode guiParent = (TreeNode)parent;
	        int count = -1;
	        for (int i = 0; i < guiParent.getChildCount();i++) {
	            if (countChild(guiParent.getChildAt(i), guiParent)) {
	                count++;
	                if (guiParent.getChildAt(i) == child) {
	                    return count;
	                }
	            }
	        }
	        return -1;
	    }


	    /**
	     * Decides wether a child should be counted while iterating all children.
	     * A child should not be counted if intermediate proofsteps are hidden and
	     * the child is not the last child, i.e. not an open or closed goal.
	     * Used by getChild, getChildCount and getIndexOfChild (implementing
	     * TreeModel).
	     */
	    protected boolean countChild(TreeNode child, TreeNode parent) {
	        if (child instanceof GUIProofTreeNode) {
	            return countChild((GUIProofTreeNode)child, parent);
	        } else if (child instanceof GUIBranchNode) {
	            return true;
	        }
	        return true;
	    }
	}

	private static class HideIntermediateFilter extends NodeFilter {

		@Override
		public boolean isActive() {
			return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getHideIntermediateProofsteps();
		}

		@Override
		void setActive(boolean active) {
			ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHideIntermediateProofsteps(active);
		}

		@Override
		public String name() {
			return "Hide Intermediate Proofsteps";
		}

		@Override
		public boolean countChild(GUIProofTreeNode node, TreeNode parent) {

			int pos = -1;
			for (int i = 0; i < parent.getChildCount();i++) {
				if (parent.getChildAt(i) == node) {
					pos = i;
					break;
				}
			}
			if (pos == parent.getChildCount() - 1) {
				return true;
			}
			// count if child is inlined by hide closed subtrees
			if (HIDE_CLOSED_SUBTREES.isActive() && !(parent.getChildAt(pos + 1) instanceof
					GUIBranchNode) &&node.getNode()
					.childrenCount() != 1) {
				return true;
			}
			return false;
		}
	}

	private static class OnlyInteractiveFilter extends NodeFilter {

		@Override
		public boolean isActive() {
			return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getHideAutomodeProofsteps();
		}

		@Override
		void setActive(boolean active) {
			ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHideAutomodeProofsteps(active);
		}

		@Override
		public String name() {
			return "Hide Non-interactive Proofsteps";
		}

		@Override
		public boolean countChild(GUIProofTreeNode node, TreeNode parent) {
			final boolean interactive = node.getNode().getNodeInfo().getInteractiveRuleApplication();
			if (interactive) return true;

			int pos = -1;
			for (int i = 0; i < parent.getChildCount();i++) {
				if (parent.getChildAt(i) == node) {
					pos = i;
					break;
				}
			}
			if (pos == parent.getChildCount() - 1) {
				return true;
			}
			// count if child is inlined by hide closed subtrees
			if (HIDE_CLOSED_SUBTREES.isActive() && !(parent.getChildAt(pos + 1) instanceof
					GUIBranchNode) &&node.getNode()
					.childrenCount() != 1) {
				return true;
			}
			return false;
		}
	}

	private static class HideClosedSubtreesFilter extends ProofTreeViewFilter {

		@Override
		public boolean isActive() {
			return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getHideClosedSubtrees();
		}

		@Override
		void setActive(boolean active) {
			ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHideClosedSubtrees(active);
		}

		@Override
		public String name() {
			return "Hide Closed Subtrees";
		}

		@Override
		boolean global() {
			return true;
		}
	}
}