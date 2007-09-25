package visualdebugger.draw2d;


import java.io.File;

import org.eclipse.draw2d.Border;
import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.Ellipse;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.Statement;

import de.uka.ilkd.key.visualdebugger.ETLeafNode;
import de.uka.ilkd.key.visualdebugger.SourceElementId;

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

