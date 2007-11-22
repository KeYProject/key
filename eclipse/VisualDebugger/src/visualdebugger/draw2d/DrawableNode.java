package visualdebugger.draw2d;

import org.eclipse.draw2d.Figure;
import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

public class DrawableNode extends Figure{
	
	private ETNode etn;
	
	public DrawableNode(ETNode etn){
		this.etn = etn;
	}
	
	public ETNode getETNode(){
		return etn;
	}

}
