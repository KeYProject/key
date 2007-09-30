package visualdebugger.draw2d;

import org.eclipse.draw2d.*;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.swt.graphics.Color;

import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.executiontree.ETMethodInvocationNode;
import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

public class MethodInvocationFigure extends Figure {

    private boolean selected;

    static final Color gradient1 = new Color(null, 132, 132, 240);

    static final Color gradient2 = new Color(null, 76, 84, 216);
    
    
    static final Color gradient12 = new Color(null, 202, 202, 210);

    static final Color gradient22 = new Color(null, 146, 154, 186);
    

    static final Color corner1 = new Color(null, 200, 208, 223);

   static final Color corner2 = new Color(null, 160, 172, 200);

    static final Color blue = new Color(null, 152, 168, 200);

    static final Color shadow = new Color(null, 202, 202, 202);

    static final int CORNER_SIZE = 00;
    
    
    final ETMethodInvocationNode miNode;
    
     ICompilationUnit unit;


    static final Border BORDER =  new LineBorder(ColorConstants.black,1);

    

    private Label label = new Label();
    
   

    


    public MethodInvocationFigure(ETMethodInvocationNode etNode){
        super();
        setBorder(BORDER);
        setLayoutManager(new StackLayout());
//        label.setText("hallo");
        add(label);
        String st="";
        if (etNode.getMethodReference()!=null)
         st= VisualDebugger.getVisualDebugger().prettyPrint(etNode.getMethodReference())+".";
        
       //etNode.getMethod().get
        st += etNode.getMethod().getProgramElementName().toString()+"(";
        ListOfTerm param = etNode.getValues();
        
        for(IteratorOfTerm it=param.iterator();it.hasNext();){
            st+= VisualDebugger.getVisualDebugger().prettyPrint(it.next());
            if (it.hasNext())
                st+= ", ";
            
        }
        
        st += ")";
        
        
        
        label.setText(st);
        miNode = etNode;
        String toolTip = "";
        


        
        toolTip += VisualDebugger.getMethodString(etNode.getMethod().getMethodDeclaration())+"\n";
        toolTip += "@"+etNode.getMethod().getContainerType().getSort()+"\n";
        if (etNode.getValues().size()>0){
        toolTip += "Parameters: \n";
        IteratorOfTerm termIt = etNode.getValues().iterator();
        for(IteratorOfProgramVariable it=etNode.getParameters().iterator();it.hasNext();){
            ProgramVariable p = it.next();
            Term val = termIt.next();
                toolTip += p.toString()+" := "+VisualDebugger.getVisualDebugger().prettyPrint(SLListOfTerm.EMPTY_LIST.append(val))+"\n";
            }        
        }
        this.setToolTip(new Label(toolTip)); 
    }
    
    
 

    /**
     * @see org.eclipse.draw2d.Figure#paintFigure(org.eclipse.draw2d.Graphics)
     */
    protected void paintFigure(Graphics g) {
        super.paintFigure(g);
        if (selected) {
            g.setForegroundColor(ColorConstants.menuBackgroundSelected);
            g.setBackgroundColor(ColorConstants.titleGradient);
        } else {        
                g.setForegroundColor(ColorConstants.white);
                g.setBackgroundColor(ColorConstants.white);
                
        
//            g.setForegroundColor(gradient1);
//            g.setBackgroundColor(gradient2);
         
        }
          g.fillGradient(getBounds().getResized(-1, -1), true);

                
                
    }

    public void setSelected(boolean value) {
        this.selected = value;
        if (selected)
            label.setForegroundColor(ColorConstants.white);
        else
            label.setForegroundColor(null);
        repaint();
    }

    /**
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return ((Label) getChildren().get(0)).getText();
    }

    public void validate() {
        repaint();
        super.validate();
    }
    
    public ETNode getETNode(){
        return miNode;
    }

 
    public ICompilationUnit getUnit() {
        //unit.get
        return unit;
    }
    
    public ASTNode getASTNode(){
  return null;
    }
    
  
}
