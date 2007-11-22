package visualdebugger.draw2d;

import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

public interface Filter {
	
	public boolean filter(ETNode etnode);

}
