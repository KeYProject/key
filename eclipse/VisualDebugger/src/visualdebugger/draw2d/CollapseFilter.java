package visualdebugger.draw2d;

import java.util.LinkedList;

import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

/**
 * The Class CollapseFilter.
 * 
 * The CollapseFilter hides all children of added ETNodes.
 */
public class CollapseFilter implements Filter {

	/** The children to hide. Ensures that children is never null. */
	LinkedList<ETNode> children = new LinkedList<ETNode>();

	/**
	 * Instantiates a new collapse filter.
	 * 
	 * @param etn
	 *            the ETNode to be collapsed.
	 */
	public CollapseFilter() {
		super();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see visualdebugger.draw2d.Filter#filter(de.uka.ilkd.key.visualdebugger.executiontree.ETNode)
	 */
	@Override
	public boolean filter(ETNode etnode) {

		// hide all nodes that are in the list of children
		if (children.contains(etnode)) {

			return false;
		}
		return true;
	}

	/**
	 * Add a node that should be collapsed.
	 * 
	 * @param etnode
	 *            the ETNode to be collapsed.
	 */
	public void addNodetoCollapse(ETNode etnode) {

		children.addAll(etnode.getChildrenList());

	}

	/**
	 * Remove a node that was collapsed. Used to expand single nodes.
	 * 
	 * @param etnode
	 *            the ETNode to be collapsed.
	 */
	public void removeNodetoCollapse(ETNode etnode) {

		LinkedList<ETNode> childrenList = etnode.getChildrenList();
		if (children.containsAll(childrenList) && childrenList.size() > 0) {
			children.removeAll(childrenList);
		}

	}

	/**
	 * Clear the list.
	 */
	public void clear() {

		if (children != null) {
			children.removeAll(children);
		}
	}

}
