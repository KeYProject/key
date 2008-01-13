package visualdebugger.draw2d;

import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

/**
 * The Class TreeFilter is used as a dummy and filters nothing. 
 * It gives back the complete tree.
 */
public class TreeFilter implements Filter {

	/* (non-Javadoc)
	 * @see visualdebugger.draw2d.Filter#filter(de.uka.ilkd.key.visualdebugger.executiontree.ETNode)
	 */
	public boolean filter(ETNode etnode) {
		return true;
	}
	

}
