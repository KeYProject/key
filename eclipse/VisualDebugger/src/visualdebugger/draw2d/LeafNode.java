package visualdebugger.draw2d;


import org.eclipse.draw2d.*;

import de.uka.ilkd.key.visualdebugger.SourceElementId;
import de.uka.ilkd.key.visualdebugger.executiontree.ETLeafNode;
import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

// TODO: Auto-generated Javadoc
/**
 * Paints a leaf node of the execution tree. A leaf node is
 * displayed as a filled circle whose color gives an indication whether
 * the state is reachable, and if so, if the program terminated
 * due to an uncaught exception or normally.
 */
public class LeafNode extends Ellipse implements DrawableNode{

    /** The Constant BORDER. */
    static final Border BORDER =          new LineBorder(ColorConstants.black,1);
    
    /** The et node. */
    final ETLeafNode etNode;

    /** The label. */
    private Label label = new Label();
    
    /** The id. */
    private  SourceElementId id=null;
    
    /** The selected. */
    private boolean selected;


 /**
  * Instantiates a new leaf node.
  * 
  * @param node the node
  */
 public LeafNode(ETLeafNode node){
     super();
     etNode=node;
     setPreferredSize(15, 15);
     setSize(15, 15);
     if (node.getState() == ETLeafNode.INFEASIBLE)
         setBackgroundColor(ColorConstants.yellow);
     else if (node.getExceptionName() != null) {
         setBackgroundColor(ColorConstants.red);
         setToolTip(new Label(node.getExceptionName()));
     } else
         setBackgroundColor(ColorConstants.green);     
 }
    
  
    /**
     * Sets the selected.
     * 
     * @param value the new selected
     */
    public void setSelected(boolean value) {
        selected = value;        
        if (selected)
            setBorder(BORDER);
        else
            setBorder(null);
        repaint();
    }

    /**
     * To string.
     * 
     * @return the string
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return this.etNode.toString();
    }

    /* (non-Javadoc)
     * @see org.eclipse.draw2d.Figure#validate()
     */
    public void validate() {
        this.setSize(15, 15);
        repaint();
        super.validate();
    }
    
    /**
     * Gets the eT leaf node.
     * 
     * @return the eT leaf node
     */
    public ETLeafNode getETLeafNode(){
        return etNode;
    }


	/* (non-Javadoc)
	 * @see visualdebugger.draw2d.DrawableNode#getETNode()
	 */
	public ETNode getETNode() {
		return etNode;
	}


}

