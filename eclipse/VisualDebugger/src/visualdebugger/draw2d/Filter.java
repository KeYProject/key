package visualdebugger.draw2d;

import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

/**
 * The Interface Filter.
 */
public interface Filter {
	
	/**
	 * Filter.
	 * 
	 * @param etnode the etnode
	 * 
	 * @return true, if the specified node should be displayed
	 */
	public boolean filter(ETNode etnode);

}
