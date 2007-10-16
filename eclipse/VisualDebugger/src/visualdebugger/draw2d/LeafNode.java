package visualdebugger.draw2d;


import org.eclipse.draw2d.*;

import de.uka.ilkd.key.visualdebugger.SourceElementId;
import de.uka.ilkd.key.visualdebugger.executiontree.ETLeafNode;

/**
 * Paints a leaf node of the execution tree. A leaf node is
 * displayed as a filled circle whose color gives an indication whether 
 * the state is reachable, and if so, if the program terminated 
 * due to an uncaught exception or normally.
 */
public class LeafNode extends Ellipse {

    static final Border BORDER =          new LineBorder(ColorConstants.black,1);
    final ETLeafNode etNode;
   // final ICompilationUnit unit;


    private Label label = new Label();
    
    private  SourceElementId id=null;
    private boolean selected;


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
    
    
    
 


    public void setSelected(boolean value) {
        selected = value;        
        if (selected)
            setBorder(BORDER);
        else
            setBorder(null);
        repaint();
    }

    /**
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return this.etNode.toString();
    }

    public void validate() {
        this.setSize(15, 15);
        repaint();
        super.validate();
    }
    
    public ETLeafNode getETLeafNode(){
        return etNode;
    }


}

