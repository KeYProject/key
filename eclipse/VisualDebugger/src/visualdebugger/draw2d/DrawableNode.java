package visualdebugger.draw2d;

import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

/**
 * The Interface DrawableNode.
 * 
 * 
 */
public interface DrawableNode {

	/**
	 * Gets the ETNode independent from its specific type.
	 * 
	 * @return the eT node
	 */
	public ETNode getETNode();
}
