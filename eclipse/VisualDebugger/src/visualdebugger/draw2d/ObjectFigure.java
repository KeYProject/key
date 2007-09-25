package visualdebugger.draw2d;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.draw2d.MouseListener;
import org.eclipse.draw2d.PositionConstants;
import org.eclipse.draw2d.ToolbarLayout;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.draw2d.graph.Node;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.widgets.Display;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ArrayOfParameterDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfProgramVariable;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SetOfProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.visualdebugger.SymbolicArrayObject;
import de.uka.ilkd.key.visualdebugger.SymbolicObject;
import de.uka.ilkd.key.visualdebugger.SymbolicObjectDiagram;

import de.uka.ilkd.key.visualdebugger.VisualDebugger;

public class ObjectFigure extends Figure{
    private Figure instanceName;

    private Label [] attrColumns;
    
   
    
    protected final SymbolicObject so;
    
    
    private MouseListener listener;

    private Figure compAttributes;

    private LinkedList sos;
    
    private Figure methodComp;

    private boolean pre;
    private final VisualDebugger vd = VisualDebugger.getVisualDebugger();

    private Label[] paramColumns; //TODO make prameter selectable

    private SymbolicObjectDiagram symbState;
    
    
  static Font BOLD = new Font(null, "", 12, SWT.BOLD);
  
  static Font BOLD_SMALL = new Font(null, "", 10, SWT.BOLD);
  
  //static Font BOLD_UNERLINE = new Font(null, "", 10, SWT.BOLD || SWT.);
  
  static Font qmFont = new Font(null, "", 30, SWT.BOLD); 
  
  
  static final Color instanceNameBackGround   = new Color(null, 222, 222, 255);




public ObjectFigure(SymbolicObject so, MouseListener listener,
            SymbolicObjectDiagram symbState,boolean pre) {
        this.so = so;
        this.sos = symbState.getSymbolicObjects();
        this.symbState = symbState;
        this.pre= pre;
        this.listener = listener;
        this.prepare();
        this.createInstanceName();
        add(instanceName);
        createCompAttributes();
        add(compAttributes);        
        createMethodComp();
        if (methodComp!=null){
            add(methodComp);
        }


    }


  


    private void createMethodComp() {
        if (so.getMethod()==null&&!pre)
            return;
        
        if (pre && !
                
         ((vd.isStaticMethod() && so.isStatic()&&so.getType().equals(vd.getType()))
         ||
                 
        ( !vd.isStaticMethod()&& so.getTerms().contains(vd.getSelfTerm()))))
            return;
        
        
        this.methodComp = new Figure();
        ToolbarLayout l = new ToolbarLayout(false);
        methodComp.setLayoutManager(l);
        
        final ProgramMethod method = pre ?  VisualDebugger.getVisualDebugger().getDebuggingMethod() : this.so.getMethod();

        Label methodSectionLabel = new Label("Current Method: ");
        if (pre)
            methodSectionLabel = new Label("Upcoming Method Invocation:");
        
        methodSectionLabel.setFont(BOLD_SMALL);
        methodComp.add(methodSectionLabel);
                    
        Label mLabel = new Label(VisualDebugger.getMethodString(method.getMethodDeclaration()));
        mLabel.setFont( Display.getCurrent().getSystemFont() );
        methodComp.add(mLabel);
        
        
        Label parameterSectionLabel = new Label("Input Values: ");
        parameterSectionLabel.setFont(BOLD_SMALL);
        methodComp.add(parameterSectionLabel);

        
        if (!pre){
        final ListOfProgramVariable parameters =so.getParameter();
        if (parameters!=null){
        this.paramColumns = new Label[parameters.size()];
        
        for(IteratorOfProgramVariable it=parameters.iterator();it.hasNext();){
            ProgramVariable p = it.next();
            Object  val = so.getValueOfParameter(p);
            if (val instanceof Term){
                Term t = (Term) val;
                Label pvLabel = new Label(p.toString()+" := "+VisualDebugger.getVisualDebugger().prettyPrint(SLListOfTerm.EMPTY_LIST.append(t),sos,so));
                
                 //= new AttributeLabel(so, p, sos);
                //System.out.println("AAAAAAAAAAA");
                //pvLabel.addMouseListener(listener);

                
                pvLabel.setFont( Display.getCurrent().getSystemFont() );
                methodComp.add(pvLabel);
            }
        }
        }
            
            
            
        }else{
            
            final ListOfTerm parameters = VisualDebugger.getVisualDebugger().getSymbolicInputValuesAsList();

            this.paramColumns = new Label[parameters.size()];
            method.getParameterDeclarationCount();
            IteratorOfTerm it = parameters.iterator();
            for(int i =0; i<method.getParameterDeclarationCount();i++){
                Term p = it.next();
                    Label pvLabel =// new Label(method.getParameterDeclarationAt(i).getVariables().getVariableSpecification(0).toString()
                            //+" := "+vd.prettyPrint(SLListOfTerm.EMPTY_LIST.append(p),sos,so));
                       //= new Label(p.toString()+" := "+VisualDebugger.getVisualDebugger().prettyPrint(SLListOfTerm.EMPTY_LIST.append(t),sos,so));                        
                         new AttributeLabel(so, (ProgramVariable)method.getParameterDeclarationAt(i).getVariables().getVariableSpecification(0).getProgramVariable(),p, sos);
                    //if ()   
                    if(!referenceSort(p.sort()))
                    pvLabel.addMouseListener(listener);
                   //    System.out.println(" bb "+(ProgramVariable)method.getParameterDeclarationAt(i).getVariables().getVariableSpecification(0).getProgramVariable() + " "+p);

                            
                    pvLabel.setFont( Display.getCurrent().getSystemFont() );
                    methodComp.add(pvLabel);
                
            }
                

            
        }
        
        methodComp.setBorder(new SeparatorBorder());
 
    
}


    private boolean referenceSort(Sort s){
        JavaInfo info = vd.getMediator().getJavaInfo();
        KeYJavaType kjt = info.getKeYJavaType(s);
       // System.out.println("KJT "+kjt);
        if(kjt==null)
            return false;
        if (kjt.getJavaType() instanceof ClassType)
            return true;
        
        return false;
    }


    private void prepare(){
        ToolbarLayout layout = new ToolbarLayout(false);
        layout.setStretchMinorAxis(true);
        layout.setMinorAlignment(ToolbarLayout.ALIGN_CENTER);
        setLayoutManager(layout);
        setBorder(new LineBorder(ColorConstants.black, 1));
        setBackgroundColor(ColorConstants.white);
        setForegroundColor(ColorConstants.black);
        setOpaque(true);
    }


    private void createInstanceName(){
        if (so.getType() instanceof ArrayType) {
              
            final String arrayType = ((ArrayType) so.getType())            
                    .getAlternativeNameRepresentation().toString();
            final String baseType = ((ArrayType) so.getType()).getBaseType().getName().toString();
            instanceName = new Label(baseType+"Array_" + so.getId() + ":" + arrayType);

        } else
            instanceName = new Label(so.getInstanceName() + ":"
                    + so.getType().getName());

       ((Label) instanceName).setTextAlignment(PositionConstants.CENTER);
        instanceName.setFont(Display.getCurrent().getSystemFont());
        instanceName.setFont(BOLD);
        if (so.isStatic())instanceName.setBorder(new MarginBorder(3, 5, 3, 5));
        else
        instanceName.setBorder(new UnderlineBorder());
        instanceName.setBackgroundColor( instanceNameBackGround);
       // instanceName.setForegroundColor(instanceNameBackGround);
        instanceName.setOpaque(true);
        // create column labels
    }


    private void createCompAttributes() {
        if (so.isUnknownObject()) {
            compAttributes = new Figure();
            Label qmLabel = new Label("?");
            qmLabel.setFont(qmFont);
            compAttributes.add(qmLabel);
            ToolbarLayout qmlayout = new ToolbarLayout(false);
            qmlayout.setMinorAlignment(ToolbarLayout.ALIGN_CENTER);
            compAttributes.setBorder(new SeparatorBorder());
            compAttributes.setLayoutManager(this.getLayoutManager());
            return;

        } 
        SetOfProgramVariable attributes = so.getAttributes().union(
                so.getAllModifiedPrimitiveAttributes());
        attrColumns = new Label[attributes.size()];
        compAttributes = new Figure();
        int i = 0;
        for (IteratorOfProgramVariable it = attributes.iterator(); it.hasNext();) {
            final ProgramVariable pv = it.next();
            attrColumns[i] = new AttributeLabel(so, pv, sos);
            attrColumns[i].addMouseListener(listener);
            compAttributes.add(attrColumns[i]);
            i++;
        }
        
        //add ref attributes that are null
        final SetOfProgramVariable pvs = so.getNonPrimAttributes();
        for (IteratorOfProgramVariable it = pvs.iterator(); it.hasNext();) {
            final ProgramVariable pv=it.next();
            if (so.getAssociationEnd(pv).isNull()){
                final Label l = new Label(pv.getProgramElementName().getProgramName() +" := null");
                l.setFont( Display.getCurrent().getSystemFont() );
                compAttributes.add(l);
            }
            
        }
        
        

        // column labels are placed in separate compartment

        compAttributes.setLayoutManager(new ToolbarLayout(false));
            compAttributes.setBorder(new SeparatorBorder());


    }

public SymbolicObject getSymbolicObject(){
    return so;
}






public class SeparatorBorder extends MarginBorder {

boolean down=false;
 private int lw=1;

 SeparatorBorder() {
        super(3, 5, 3, 5);
    }
 
 SeparatorBorder(boolean down){
     this();
     this.down = down;
 }
 
 
 
 
 


SeparatorBorder(int lw) {
    super(3, 5, 3, 5);
    this.lw = lw;
  
}



       public void paint(IFigure figure, Graphics graphics, Insets insets) {
               Rectangle where = getPaintRectangle(figure, insets);
               graphics.setLineWidth(lw);
               if (down){
                   graphics.setLineWidth(2);
                   graphics.drawLine(where.getBottomLeft().getTranslated(0, -3), where.getBottomRight().getTranslated(0, -3));
               }
               else
               graphics.drawLine(where.getTopLeft(), where.getTopRight());
              
       }



 }

public class UnderlineBorder extends MarginBorder {

    
    
    UnderlineBorder() {
        super(3, 7, 3, 7);
       
      
    }

    

           public void paint(IFigure figure, Graphics graphics, Insets insets) {
                 //  Rectangle where = getPaintRectangle(figure, insets);
                       graphics.setLineWidth(2);
                       Label l = (Label) figure;
                       Rectangle tb = l.getTextBounds();
                       
                       Point left = tb.getBottomLeft().translate(0, 0);
                       Point right = tb.getBottomRight().translate(0, 0);
                       graphics.drawLine(left, right);
                       
                       //graphics.drawLine(where.getBottomLeft().getTranslated(0, -3), where.getBottomRight().getTranslated(0, -3));
                  
           }



     }


    public class AttributeLabel extends Label{
        private final SymbolicObject so;
        private final ProgramVariable pv;
        private boolean selected=false;
        private Term valueterm;
        
        public AttributeLabel(SymbolicObject so, ProgramVariable pv,LinkedList sos){
           super();           
           this.so = so ;
           this.pv = pv;
           String text = pv.getProgramElementName().getProgramName();
           if (so.getAllModifiedPrimitiveAttributes().contains(pv)){
               text = text+ " := "+VisualDebugger.getVisualDebugger().prettyPrint(SLListOfTerm.EMPTY_LIST.append(so.getValueTerm(pv)),sos,so);
           }   else if (so.getValueOfParameter(pv)!=null)
               text = text+ " := "+VisualDebugger.getVisualDebugger().prettyPrint(SLListOfTerm.EMPTY_LIST.append(so.getValueOfParameter(pv)),sos,so);
           setText(text);
           setFont( Display.getCurrent().getSystemFont() );
        }
        
        
        public AttributeLabel(SymbolicObject so, ProgramVariable pv, Term value,LinkedList sos){
            super();           
            this.so = so ;
            this.pv = pv;
            this.valueterm = value;
            String text = pv.getProgramElementName().getProgramName();
                text = text+ " := "+VisualDebugger.getVisualDebugger().prettyPrint(value,sos,so);
            setText(text);
            setFont( Display.getCurrent().getSystemFont() );
         }


        public ProgramVariable getPv() {
            return pv;
        }

        public SymbolicObject getSo() {
            return so;
        }
        
        public void setSelected(boolean value) {
            this.selected = value;
            if (selected)
                this.setForegroundColor(ColorConstants.blue);
            else
                this.setForegroundColor(null);
            repaint();
        }


        public Term getValueterm() {
            return valueterm;
        }
        
       
        
    }

}