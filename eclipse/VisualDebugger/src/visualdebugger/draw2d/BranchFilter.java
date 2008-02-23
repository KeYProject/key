package visualdebugger.draw2d;

import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;
import de.uka.ilkd.key.visualdebugger.executiontree.ETPath;

/**
 * The Class BranchFilter.
 * 
 * This Class allows us to display only a certain branch of
 * the execution tree specified by the path.
 */
public class BranchFilter implements Filter{
 
	/** The path. */
	ETPath path;

	/**
	 * Instantiates a new branch filter.
	 * 
	 * @param etPath the branch we want to display
	 */
	public BranchFilter(ETPath etPath) {
	path = etPath;
	}

	/* (non-Javadoc)
	 * @see visualdebugger.draw2d.Filter#filter(de.uka.ilkd.key.visualdebugger.executiontree.ETNode)
	 */
	public boolean filter(ETNode et) {
	return path.contains(et);
	}

    public ETPath getPath() {
        return path;
    }

}
