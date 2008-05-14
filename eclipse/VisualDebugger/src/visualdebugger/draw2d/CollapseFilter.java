package visualdebugger.draw2d;

import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

/**
 * The Class CollapseFilter.
 * 
 * The CollapseFilter hides all children of added ETNodes.
 */
public class CollapseFilter implements Filter {

	/** The children to hide. Ensures that children is never null. */
	private LinkedList<ETNode> children = new LinkedList<ETNode>();

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
	 * @return true, if the etnode is not in registered to this filter
	 */
	public boolean filter(ETNode etnode) {

		// hide all nodes that are in the list of children
			return !children.contains(etnode);

	}

	/**
	 * Add a node that should be collapsed.
	 * 
	 * @param etnode
	 *            the ETNode to be collapsed.
	 */
	public void addNodetoCollapse(ETNode etnode) {

		etnode.setCollapsed(true);
		children.addAll(etnode.getChildrenList());

	}

	/**
	 * Remove a node that was collapsed. Used to expand single nodes.
	 * 
	 * @param etnode
	 *            the ETNode to be collapsed.
	 */

	public void removeNodetoCollapse(ETNode etnode) {

		etnode.setCollapsed(false);
		LinkedList<ETNode> childrenList = etnode.getChildrenList();
		if (children.containsAll(childrenList) && childrenList.size() > 0) {
			children.removeAll(childrenList);
		}

	}

	/**
	 * Clear the list.
	 */
	public void clear() {

		children = new LinkedList<ETNode>();
	}

	/**
	 * Remove the overlays indicating that a node is collapsed
	 * beginning from the passed ETNode.
	 */
	public void clearCollapseMarkers(ETNode etn) {

		etn.setCollapsed(false);
		Iterator<ETNode> childrenIterator = etn.getChildrenList().iterator();
		while (childrenIterator.hasNext()) {
			ETNode theNode = (ETNode) childrenIterator.next();
			theNode.setCollapsed(false);
			clearCollapseMarkers(theNode);
		}

	}

}
