package visualdebugger.views;

import java.util.*;

import org.eclipse.draw2d.*;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.draw2d.graph.DirectedGraph;
import org.eclipse.draw2d.graph.DirectedGraphLayout;
import org.eclipse.draw2d.graph.Edge;
import org.eclipse.draw2d.graph.Node;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.*;
import org.eclipse.swt.widgets.Button;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;

import visualdebugger.draw2d.ArrayObjectFigure;
import visualdebugger.draw2d.FixedConnectionAnchor;
import visualdebugger.draw2d.ObjectFigure;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IteratorOfProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.visualdebugger.DebuggerEvent;
import de.uka.ilkd.key.visualdebugger.DebuggerListener;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.statevisualisation.StateVisualization;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicArrayObject;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicObject;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicObjectDiagram;

public class SymbolicStateView extends ViewPart implements DebuggerListener {

    private SymbolicObjectDiagram currentState = null;

    private boolean preState = true;

    private StateVisualization stateVis = null;
    
    private SetOfTerm[] possibleIndexTerms; 

    private Shell shell;

    private Composite parent;

    private FigureCanvas figureCanvas;

    private Layer figures;

    private IFigure root;

    private ConnectionLayer connections;

    private Slider prestateForTracesSlider;

    private org.eclipse.swt.widgets.List constraintsList;

    private LinkedList symbolicObjects;

    private Object selectedAttr;

    private final VisualDebugger vd;

    private Slider arrayIndexSlider;

    private Button preButton;

    private Button postButton;

    private FanRouter frouter;

    public SymbolicStateView() {
        vd = VisualDebugger.getVisualDebugger();
        vd.addListener(this);
    }

    /**
     * This is a callback that will allow us to create the viewer and initialize
     * it.
     */
    public void createPartControl(Composite parent) {
        shell = parent.getShell();
        this.parent = parent;
        parent.setLayout(new GridLayout(2, false));
        figureCanvas = new FigureCanvas(parent, SWT.NONE);
        figureCanvas.getViewport().setContentsTracksHeight(true);
        figureCanvas.getViewport().setContentsTracksWidth(true);
        figureCanvas.getViewport().setContentsTracksHeight(true);
        figureCanvas.getViewport().setContentsTracksWidth(true);
        figureCanvas.setLayoutData(new GridData(GridData.FILL_BOTH));
       
        root = new LayeredPane();
        figures = new Layer();
        connections = new ConnectionLayer();
        frouter = new FanRouter();
        frouter.setSeparation(40);
        frouter.setNextRouter(new ShortestPathConnectionRouter(figures));
         connections.setAntialias(SWT.ON);
        root.add(figures);
        root.add(connections);
        FlowLayout layout = new FlowLayout();
        layout.setHorizontal(false);
        layout.setStretchMinorAxis(false);
        layout.setMajorSpacing(50);
        layout.setMinorSpacing(50);
        figures.setLayoutManager(layout);
        figures.setLayoutManager(new XYLayout());
        figureCanvas.setContents(root);
        hookShell();
        shell.redraw();
        shell.open();
        if (vd.getCurrentState() != null) {
            stateVis = vd.getCurrentState();
            refreshPCStates();
        }
    }

    private void hookShell() {
        Composite localShell = new Composite(parent, 0);
        localShell.setLayoutData(new GridData(GridData.FILL_VERTICAL));

        localShell.setLayout(new GridLayout());
        Group rootGroup = new Group(localShell, 0);
        rootGroup.setText("Instance Configuation");
        rootGroup.setLayoutData(new GridData(200,SWT.DEFAULT));
        FontData data = rootGroup.getFont().getFontData()[0];
        data.setStyle(SWT.BOLD);
        rootGroup.setLayout(new GridLayout());

        prestateForTracesSlider = new Slider(rootGroup, SWT.HORIZONTAL);

        prestateForTracesSlider.setEnabled(true);
        prestateForTracesSlider.setMaximum(1);
        prestateForTracesSlider.setMinimum(0);
        prestateForTracesSlider.setSelection(0);
        prestateForTracesSlider.setIncrement(1);
        prestateForTracesSlider.setPageIncrement(1);

        
        prestateForTracesSlider.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
                final int sel = prestateForTracesSlider.getSelection();
                possibleIndexTerms= stateVis.getPossibleIndexTermsForPcState(sel);
                if (possibleIndexTerms.length>0)
                    currentState = stateVis.getSymbolicState(sel, possibleIndexTerms[0],true);
                else throw new RuntimeException();
                arrayIndexSlider.setSelection(0);
                arrayIndexSlider.setMaximum(possibleIndexTerms.length);
                refreshVisualizedState();
            }
        });

        Group rootGroup2 = new Group(localShell, 0);
        rootGroup2.setLayoutData(new GridData(200,SWT.DEFAULT));
        rootGroup2.setText("Array Index Configuration");      
        rootGroup2.setLayout(new GridLayout());

        arrayIndexSlider = new Slider(rootGroup2, SWT.HORIZONTAL);
        arrayIndexSlider.setEnabled(true);
        arrayIndexSlider.setMaximum(1);
        arrayIndexSlider.setMinimum(0);
        arrayIndexSlider.setSelection(0);
        arrayIndexSlider.setIncrement(1);
        arrayIndexSlider.setPageIncrement(1);
                
        arrayIndexSlider.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
                if (preState)
                currentState = stateVis.getSymbolicState(prestateForTracesSlider.getSelection(),(SetOfTerm) possibleIndexTerms[arrayIndexSlider.getSelection()],true);
                else 
                currentState = stateVis.getSymbolicState(prestateForTracesSlider.getSelection(),(SetOfTerm) possibleIndexTerms[arrayIndexSlider.getSelection()],false);               
                refreshVisualizedState();
            }
        });
        
        
        Group rootGroup3 = new Group(localShell, 0);
        rootGroup3.setLayoutData(new GridData(200,SWT.DEFAULT));      
        rootGroup3.setLayout(new GridLayout());


        preButton = new Button(rootGroup3, SWT.RADIO);
        preButton.setText("Prestate");
        preButton.setSelection(true);
        preButton.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
                //preButton.getS
                preState = preButton.getSelection();
                    currentState = stateVis.getSymbolicState(prestateForTracesSlider.getSelection(),
                           possibleIndexTerms[arrayIndexSlider.getSelection()],true);
                refreshVisualizedState();              
            }
        });

        postButton = new Button(rootGroup3, SWT.RADIO);
        postButton.setText("Poststate");
        postButton.setSelection(false);
        postButton.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
                preState = !postButton.getSelection();
                currentState = stateVis.getSymbolicState(prestateForTracesSlider.getSelection(),(SetOfTerm)possibleIndexTerms[arrayIndexSlider.getSelection()],false);                          
                refreshVisualizedState();
            }
        });

        Group bcGroup = new Group(localShell, 0);
        bcGroup.setBackground(ColorConstants.white);
        bcGroup.setText("Constraints");
        bcGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
        bcGroup.setLayout(new GridLayout());
        constraintsList = new org.eclipse.swt.widgets.List(bcGroup, SWT.WRAP
                | SWT.V_SCROLL | SWT.H_SCROLL);
        constraintsList.setLayoutData(new GridData(GridData.FILL_BOTH));
        constraintsList.setBackground(ColorConstants.white);

    }

    private void startRefreshThread() {
        Display display = shell.getDisplay();
        final Thread barThread = new Thread("Refresh Symbolic State View Thread") {
            public void run() {
                refreshPCStates();
            }
        };
        display.asyncExec(barThread);
    }
    
    

    private void refreshPCStates() {

        prestateForTracesSlider.setMinimum(0);
        if (stateVis != null) {
            prestateForTracesSlider.setMaximum(stateVis.numberOfPCStates());
            prestateForTracesSlider.setIncrement(1);
            prestateForTracesSlider.setPageIncrement(1);
            prestateForTracesSlider.setThumb(1);
            prestateForTracesSlider.setSelection(0);
            prestateForTracesSlider.setEnabled(true);
            
            preButton.setSelection(true);
            postButton.setSelection(false);
            preButton.setEnabled(true);
            postButton.setEnabled(true);
            preState=true;
            possibleIndexTerms= stateVis.getPossibleIndexTermsForPcState(0);
           if (possibleIndexTerms.length>0) {
                currentState = stateVis.getSymbolicState(0,possibleIndexTerms[0],true);
           }
            else throw new RuntimeException("No States to visualize");
            arrayIndexSlider.setMaximum(possibleIndexTerms.length);            
            arrayIndexSlider.setSelection(0);
            arrayIndexSlider.setEnabled(true);

            try {
                refreshVisualizedState();
            } catch (RuntimeException re) {
                re.printStackTrace();
                System.out.println(re.getMessage());
            }
        }else{
            prestateForTracesSlider.setEnabled(false);
            prestateForTracesSlider.setMaximum(1);
            prestateForTracesSlider.setMinimum(0);
            prestateForTracesSlider.setSelection(0);
            prestateForTracesSlider.setIncrement(1);
            prestateForTracesSlider.setPageIncrement(1);
            arrayIndexSlider.setEnabled(false);
            arrayIndexSlider.setMaximum(1);
            arrayIndexSlider.setMinimum(0);
            arrayIndexSlider.setSelection(0);
            arrayIndexSlider.setIncrement(1);
            arrayIndexSlider.setPageIncrement(1);
            preButton.setSelection(true);
            postButton.setSelection(false);
            preButton.setEnabled(false);
            postButton.setEnabled(false                    );
            figures.removeAll();
            connections.removeAll();
            this.setConstraints(null, null, null);
        }
    }
    
    
    
    

    private synchronized void refreshVisualizedState() {
        if (currentState == null)
            return;
        symbolicObjects = currentState.getSymbolicObjects();

        figures.removeAll();
        connections.removeAll();
        final HashMap node2figure = new HashMap();
        final HashMap figure2node = new HashMap();

        final DirectedGraph graph = new DirectedGraph();
        graph.setDefaultPadding(new Insets(50));

        // create object figure and nodes
        for (Iterator soIt = symbolicObjects.iterator(); soIt.hasNext();) {
            final SymbolicObject so = (SymbolicObject) soIt.next();
            if (!so.isNull()){
            final ObjectFigure f = createFigure(so);
            final Node n = new Node();
            f.validate();
            n.setSize(f.getPreferredSize());
            graph.nodes.add(n);
            node2figure.put(n, f);
            figure2node.put(f, n);
            }
        }

        // create edges

        for (Iterator ofIt = figure2node.keySet().iterator(); ofIt.hasNext();) {
            final ObjectFigure ofStart = (ObjectFigure) ofIt.next();
            for (Iterator soEndsIt = ofStart.getSymbolicObject()
                    .getAllAssociationEnds().iterator(); soEndsIt.hasNext();) {
                SymbolicObject soEnd = (SymbolicObject) soEndsIt.next();
                if (!soEnd.isNull()){
                final ObjectFigure ofEnd = getOFbySO(figure2node.keySet(),
                        soEnd);
                if (ofEnd != ofStart) {
                    final Edge edge = new Edge((Node) figure2node.get(ofStart),
                            (Node) figure2node.get(ofEnd));

                    edge.setPadding(100);
                    graph.edges.add(edge);
                }
                }
            }
        }

        // layout graph
        graph.setDirection(PositionConstants.EAST);
        new DirectedGraphLayout().visit(graph);

        // add figures
        for (int i = 0; i < graph.nodes.size(); i++) {
            Node node = graph.nodes.getNode(i);
            buildNodeFigure(figures, node, (ObjectFigure) node2figure.get(node));
        }

        figures.validate(); // TODO warum ?
        int offset = 0;

        // create and add connections
        for (Iterator ofIt = figure2node.keySet().iterator(); ofIt.hasNext();) {
            final ObjectFigure ofStart = (ObjectFigure) ofIt.next();

            for (Iterator<ProgramVariable> pvIt = ofStart.getSymbolicObject()
                    .getNonPrimAttributes().iterator(); pvIt.hasNext();) {
                ProgramVariable pv = pvIt.next();
                final SymbolicObject soEnd = ofStart.getSymbolicObject()
                        .getAssociationEnd(pv);
                if (!soEnd.isNull()){
                final ObjectFigure ofEnd = getOFbySO(figure2node.keySet(),
                        soEnd);

                if (ofStart == ofEnd) { // loop connection
                    connections.add((createSelfConnection(ofStart, pv
                            .getProgramElementName().getProgramName()
                            .toString(), offset++)));
                } else {
                    connections.add((createConnection(ofStart, ofEnd, pv
                            .getProgramElementName().getProgramName()
                            .toString())));
                }
                }
            }

            if (ofStart instanceof ArrayObjectFigure
                    && !((SymbolicArrayObject)((ArrayObjectFigure) ofStart).getSymbolicObject())
                            .isPrimitiveType()) {
                ArrayObjectFigure aofStart = (ArrayObjectFigure) ofStart;
                SymbolicArrayObject saoStart = ((SymbolicArrayObject)aofStart.
                        getSymbolicObject());

                for (Iterator<Term> indexIt = saoStart.getAllIndexTerms().iterator(); indexIt
                        .hasNext();) {
                    Term index = indexIt.next();
                    SymbolicObject soEnd = ((SymbolicArrayObject)aofStart.getSymbolicObject())
                            .getAssociationEndForIndex(index);
                    if (!soEnd.isStatic()){
                    final HashMap index2y = aofStart.getIndexY();
                    final ObjectFigure ofEnd = getOFbySO(figure2node.keySet(), soEnd);
                    connections.add((createArrayConnection(ofStart,
                            ((Integer) index2y.get(index)).intValue(), ofEnd,"")));
                    }

                }
            }

        }
    }

    static void buildNodeFigure(Figure contents, Node node, ObjectFigure of) {
        contents.add(of, new Rectangle(node.x, node.y, node.width, node.height));
        new Dragger(of);
    }

    private ObjectFigure getOFbySO(Collection objectFigures,
            SymbolicObject toFind) {
        Iterator it = objectFigures.iterator();
        while (it.hasNext()) {
            ObjectFigure of = (ObjectFigure) it.next();
            if (of.getSymbolicObject() == toFind) {
                return of;
            }

        }
        System.err.println("ObjectFigure not found");
        return null;
    }

    private ObjectFigure createFigure(SymbolicObject o) {
        if (o instanceof SymbolicArrayObject)

            return new ArrayObjectFigure((SymbolicArrayObject) o,
                    new MouseListener.Stub() {
                        public void mousePressed(MouseEvent me) {
                            setSelected(me.getSource());
                        }

                        public void mouseDoubleClicked(MouseEvent me) {
                            //        doExpandCollapse();
                        }
                    }, currentState,this.preState);

        else

            return new ObjectFigure(o, new MouseListener.Stub() {
                public void mousePressed(MouseEvent me) {
                    setSelected(me.getSource());
                }

                public void mouseDoubleClicked(MouseEvent me) {

                }
            }, currentState,this.preState);
    }
    
    
    

    private void setSelected(Object o) {
        if (o instanceof ObjectFigure.AttributeLabel) {
            ObjectFigure.AttributeLabel al = (ObjectFigure.AttributeLabel) o;
            if (this.selectedAttr != null) {
                if (selectedAttr instanceof ObjectFigure.AttributeLabel)
                    ((ObjectFigure.AttributeLabel) selectedAttr)
                            .setSelected(false);
                else
                    ((ArrayObjectFigure.IndexLabel) selectedAttr)
                            .setSelected(false);
            }
            al.setSelected(true);
            this.selectedAttr = al;
            if (al.getSo().getAttributes().contains(al.getPv()))
                this.setConstraints(al.getSo()
                        .getAttrConstraints(al.getPv()), symbolicObjects, al
                        .getSo());
            else     {   
                this.setConstraints(currentState.getConstraints(al.getValueterm()),symbolicObjects,al.getSo());
            }

//            else
//                this.setConstraints(null,null,null);
        } else if (o instanceof ArrayObjectFigure.IndexLabel) {
            ArrayObjectFigure.IndexLabel al = (ArrayObjectFigure.IndexLabel) o;
            if (this.selectedAttr != null) {
                if (selectedAttr instanceof ObjectFigure.AttributeLabel)
                    ((ObjectFigure.AttributeLabel) selectedAttr)
                            .setSelected(false);
                else
                    ((ArrayObjectFigure.IndexLabel) selectedAttr)
                            .setSelected(false);

            }
            al.setSelected(true);
            this.selectedAttr = al;
            if (al.getSo().getConstraintsForIndex(al.getIndex()) != ImmSLList.<Term>nil())
                setConstraints(al.getSo()
                        .getConstraintsForIndex(al.getIndex()), symbolicObjects,
                        al.getSo());
            else
               setConstraints(null, null, null);

        }    else if (o instanceof ArrayObjectFigure.IndexConstraintLabel) {
            ArrayObjectFigure.IndexConstraintLabel al = (ArrayObjectFigure.IndexConstraintLabel) o;
            this.currentState.getIndexTerms();
            SetOf<Term> indexConstr = al.getIndexConstraints();
            for(Iterator it = this.symbolicObjects.iterator(); it.hasNext();){
                SymbolicObject next = (SymbolicObject) it.next();
                if (next instanceof SymbolicArrayObject){
                    SymbolicArrayObject sao = (SymbolicArrayObject)next;
                    if (sao != al.getSo()){
                     indexConstr = indexConstr.union(sao.getIndexConfiguration());   
                    }
                }
               
            }

            int result =-1; 
            int i=0;
            for(int j = 0 ; j< possibleIndexTerms.length;j++){
                SetOf<Term> next = (SetOf<Term> ) possibleIndexTerms[j];
               // System.out.println("checking"+next);
                if (next.subset(indexConstr)&& indexConstr.subset(next)){
                    result = i;
                }
                i++;
            }

            if (result>-1){
                if (!preState) {
                    currentState = stateVis.getSymbolicState(prestateForTracesSlider.getSelection(),possibleIndexTerms[result],false);
                } else {
                    currentState = stateVis.getSymbolicState(prestateForTracesSlider.getSelection(),possibleIndexTerms[result],true);
                }
                arrayIndexSlider.setSelection(result);
                refreshVisualizedState();
            } else {
                MessageDialog.openInformation(PlatformUI.getWorkbench()
                        .getActiveWorkbenchWindow().getShell(),
                        "Array Index Constraints Infeasible",
                        "The chosen array index constraints are infeasible."+
                        "Please choose another combination or use the slider " +
                        "in order to discover all possible combinations"
                                );                
            }
        }        
    }
    
    
    private void setConstraints(IList<Term> cons, LinkedList sos, SymbolicObject so){
        if (cons!=null){            
            final Term[] conArray = cons.toArray();
            final  String[] termsString =new String[conArray.length];             
            //text.setItems();
            for(int i=0;i<conArray.length;i++){
                termsString[i]=(vd.prettyPrint(conArray[i],sos,so));    
            }            
            this.constraintsList.setItems(termsString);
        } else constraintsList.setItems(new String[0]);        
    }
    
    
    

    private Connection createSelfConnection(IFigure figFrom, String text,
            int offset) {
        PolylineConnection con = new PolylineConnection();
        Rectangle bounds = figFrom.getBounds();

        FixedConnectionAnchor fcAnchor = new FixedConnectionAnchor(figFrom);
        fcAnchor.setOffsetH(bounds.width / 4);
        con.setSourceAnchor(fcAnchor);

        fcAnchor = new FixedConnectionAnchor(figFrom);
        fcAnchor.setOffsetH(bounds.width / 4 + bounds.width / 2);

        con.setTargetAnchor(fcAnchor);

        BendpointConnectionRouter router = new BendpointConnectionRouter();
        con.setConnectionRouter(router);
        ArrayList list = new ArrayList();

        RelativeBendpoint b = new RelativeBendpoint(con);
        b.setWeight(0.2f);
        Dimension d1 = new Dimension(0, -25 - offset * 20);
        Dimension d2 = new Dimension(0, -25 - offset * 20);

        b.setRelativeDimensions(d1, d2);
        list.add(b);

        b = new RelativeBendpoint(con);
        b.setWeight(0.8f);
        d1 = new Dimension(0, -25 - offset * 20);
        d2 = new Dimension(0, -25 - offset * 20);
        b.setRelativeDimensions(d1, d2);

        list.add(b);

        con.setRoutingConstraint(list);
        con.setRoutingConstraint(list);
        PolygonDecoration decoration = new PolygonDecoration();
        decoration.setTemplate(PolygonDecoration.TRIANGLE_TIP);
        decoration.setScale(8, 4);
        con.setTargetDecoration(decoration);
        Label label = createConnectionLabel(text);
        con.add(label, new MidpointLocator(con, 1));
        return con;

    }

    private Label createConnectionLabel(String text) {
        Label result = new Label(text);
        result.setBackgroundColor( ColorConstants.white );
        result.setBorder(new LineBorder(ColorConstants.black));
        result.setOpaque(true);
        return result;
    }

    private Connection createConnection(IFigure figFrom, IFigure figTo,
            String text) {

        figFrom.validate();

        PolylineConnection con = new PolylineConnection();
        con.setSourceAnchor(new ChopboxAnchor(figFrom));
        con.setTargetAnchor(new ChopboxAnchor(figTo));

        con.setConnectionRouter(frouter);

        PolygonDecoration decoration = new PolygonDecoration();
        decoration.setTemplate(PolygonDecoration.TRIANGLE_TIP);
        decoration.setScale(8, 4);
        con.setTargetDecoration(decoration);
        Label label = createConnectionLabel(text);
      
        con.add(label, new MidpointLocator(con, 0));
        return con;

    }

    private Connection createArrayConnection(IFigure figFrom, int y,
            IFigure figTo, String text) {
        PolylineConnection con = new PolylineConnection();
        con.setConnectionRouter(frouter);
        

        con.setTargetAnchor(new ChopboxAnchor(figTo));

        FixedConnectionAnchor fcAnchor = new FixedConnectionAnchor(figFrom);
        //System.out.println("Fig bounds " + figFrom.getBounds());
        fcAnchor.setOffsetH(figFrom.getBounds().width);

        fcAnchor.setOffsetV(y);
        con.setSourceAnchor(fcAnchor);

        PolygonDecoration decoration = new PolygonDecoration();
        decoration.setTemplate(PolygonDecoration.TRIANGLE_TIP);
        decoration.setScale(8, 4);
        con.setTargetDecoration(decoration);
//        Label label = createConnectionLabel(text);
//   
//        con.add(label, new MidpointLocator(con, 0));
        return con;
    }

    /**
     * Passing the focus request to the viewer's control.
     */
    public void setFocus() {

    }

    public synchronized void update(DebuggerEvent event) {
        if (event.getType() == DebuggerEvent.VIS_STATE) {
            stateVis = (StateVisualization) event.getSubject();
            startRefreshThread();
        } else if (event.getType() == DebuggerEvent.PROJECT_LOADED_SUCCESSFUL) {
            stateVis = null;
            startRefreshThread();
        }
    }

    static class Dragger extends MouseMotionListener.Stub implements
            MouseListener {
        public Dragger(IFigure figure) {
            figure.removeMouseMotionListener(this);
            figure.removeMouseListener(this);                
            
            figure.addMouseMotionListener(this);
            figure.addMouseListener(this);
        }

        Point last;

        public void mouseReleased(MouseEvent e) {
        }

        public void mouseClicked(MouseEvent e) {
        }

        public void mouseDoubleClicked(MouseEvent e) {
        }

        public void mousePressed(MouseEvent e) {
            last = e.getLocation();
            e.consume();
        }

        public void mouseDragged(MouseEvent e) {
            Point p = e.getLocation();            
            
            if (last!=null){
           // {
                Dimension delta = p.getDifference(last);
                Figure f = ((Figure) e.getSource());
                f.setBounds(f.getBounds().getTranslated(delta.width, delta.height));
            }
            last = p;
        }
    }

}
