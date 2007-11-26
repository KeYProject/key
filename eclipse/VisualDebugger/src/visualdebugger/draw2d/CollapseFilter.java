package visualdebugger.draw2d;

import java.util.LinkedList;

import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

/**
 * The Class CollapseFilter.
 * 
 * The CollapseFilter hides all children of the passed ETNode.
 */
public class CollapseFilter implements Filter {

	/** The node to be collapsed */
	ETNode etn = null;
	LinkedList children = null;

	/**
	 * Instantiates a new collapse filter.
	 * 
	 * @param etn
	 *            the ETNode to be collapsed.
	 */
	public CollapseFilter(ETNode etn) {
		super();
		this.etn = etn;
		this.children = etn.getChildrenList();
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

}
