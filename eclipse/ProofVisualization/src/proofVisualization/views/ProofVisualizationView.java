package proofVisualization.views;

import java.net.URL;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.ITextOperationTarget;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.DrillDownAdapter;
import org.eclipse.ui.part.ViewPart;
import org.osgi.framework.Bundle;

import proofVisualization.ProofVisualizationPlugin;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.visualization.ContextTraceElement;
import de.uka.ilkd.key.visualization.ExecutionTraceModel;
import de.uka.ilkd.key.visualization.ParentContextTraceElement;
import de.uka.ilkd.key.visualization.ProofVisualization;
import de.uka.ilkd.key.visualization.TraceElement;
import de.uka.ilkd.key.visualization.VisualizationModel;


public class ProofVisualizationView extends ViewPart {
    private TreeViewer viewer;

    private DrillDownAdapter drillDownAdapter;
    private Action visualizeNodeAction;
    private Action markNodeAction;
    private Action toNodeAction;
    private Action doubleClickAction;
    private Action rmAnnotationsAction;
    private Action stepIntoAction, stepOverAction;
    
    private ParentContextTraceElement invisibleRoot;
    private ExecutionTraceModel trace;
    private VisualizationModel visualizationModel=null;
    private LinkedList sViewerList = new LinkedList();

    
    private static String MARKER = "ProofVisualization.PVAnnotationType";
    private static String LAST_MARKER ="ProofVisualization.PVAnnotationType2";
    private static String EXC_MARKER ="ProofVisualization.PVAnnotationType3";
   

    class ViewContentProvider implements IStructuredContentProvider, 
                                           ITreeContentProvider {
        

        public void inputChanged(Viewer v, Object oldInput, Object newInput) {
        }
        
        public void dispose() {
        }
        
        public Object[] getElements(Object parent) {
            if (parent.equals(getViewSite())) {
                if (invisibleRoot==null) initialize();
                return getChildren(invisibleRoot);
            }
            return getChildren(parent);
        }
        
        public Object getParent(Object child) {
           if (child instanceof TraceElement) {
                    if (((ContextTraceElement)child).getParent()==TraceElement.PARENTROOT) 
                        return invisibleRoot; 
           	    return ((ContextTraceElement)child).getParent();
                    }
           return null;
        }

        public Object [] getChildren(Object parent) {
                if (parent==invisibleRoot) 
                        return collectTopLevelElements(invisibleRoot);
                if (parent instanceof ParentContextTraceElement)
                        return ((ParentContextTraceElement)parent).getChildren();
                return new Object[0];
        }
        
        private Object[] collectTopLevelElements(ParentContextTraceElement root){
            ArrayList children = new ArrayList();
                ContextTraceElement che = root.getNextExecuted();
                while ((che!=TraceElement.END)&& 
                        (TraceElement.PARENTROOT ==che.getParent())){
                	children.add(che);
                	if (che instanceof ParentContextTraceElement)
                	        che =((ParentContextTraceElement)che).stepOver();
                	else che=che.getNextExecuted();
                }
                return children.toArray();
        }
        
        public boolean hasChildren(Object parent) {
            return (parent instanceof ParentContextTraceElement)&& 
            ((ParentContextTraceElement)parent).getChildren().length>0;
        }

 
        private void initialize() {
                invisibleRoot = new ParentContextTraceElement();
        }
 
    
    }
  
    
    class ViewLabelProvider extends LabelProvider {

    	private String getTreeLabel(ContextTraceElement cte){
    	         String s = cte.getSrcElement().toString();
                if (cte.getContextStatement()!=null)
                    s = cte.getContextStatement().toString();
    		int i= s.indexOf("\n");
    		if (i>-1) return s.substring(0,i);
    		return s;
        }
        
        public String getText(Object obj) {
                if (obj instanceof ContextTraceElement) 
                        return getTreeLabel((ContextTraceElement)obj);
                return "unknown tree content";
        }

        public Image getImage(Object obj) {
            String imageKey = null;//ISharedImages.IMG_OBJ_ELEMENT;
            if ((((TraceElement)obj).serialNr()==trace.getLastContextTraceElement().serialNr())&& 
            		trace.uncaughtException())
                return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJS_ERROR_TSK);
            if (obj instanceof ParentContextTraceElement){
               imageKey = ISharedImages.IMG_OBJ_FOLDER;
               return PlatformUI.getWorkbench().getSharedImages().getImage(imageKey);
            }
            return null;
        }
    }
    
    
    class NameSorter extends ViewerSorter {
		public int compare(Viewer viewer, Object o1, Object o2){
			if (!(o1 instanceof TraceElement)|| 
			                !(o2 instanceof TraceElement))
			        return 0;
			TraceElement h1 = (TraceElement) o1;
			TraceElement h2 = (TraceElement) o2;
			return h1.serialNr()-h2.serialNr();
		}
	}

    
    
    
 
    
    
    public ProofVisualizationView() {
    }

    /**
     * This is a callback that will allow us
     * to create the viewer and initialize it.
     */
    public void createPartControl(Composite parent) {
        viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
        drillDownAdapter = new DrillDownAdapter(viewer);
        viewer.setContentProvider(new ViewContentProvider());
        viewer.setLabelProvider(new ViewLabelProvider());
        viewer.setSorter(new NameSorter());
        viewer.setInput(getViewSite());
        viewer.addSelectionChangedListener(new ISelectionChangedListener(){
        public void selectionChanged(SelectionChangedEvent event){
		  
	         }
        });
        hookListener();
        makeActions();
        hookContextMenu();
        hookDoubleClickAction();
        contributeToActionBars();
    }
    
    private void hookListener(){
        viewer.addSelectionChangedListener(new ISelectionChangedListener() {
            public void selectionChanged(SelectionChangedEvent event) {
                // if the selection is empty clear the label
                if(event.getSelection().isEmpty()) {
                    
                    return;
                }
                if(event.getSelection() instanceof IStructuredSelection) {
                    IStructuredSelection selection = (IStructuredSelection)event.getSelection();
                    for (Iterator iterator = selection.iterator(); iterator.hasNext();) {
                        removeAnnotionMarkers();
                        Object domain = iterator.next();
                        if (domain instanceof ContextTraceElement)
                        visualizeTraceElement((ContextTraceElement)domain,false);
                    }
                }
            }
         });
    }

    private void hookContextMenu() {
        MenuManager menuMgr = new MenuManager("#PopupMenu");
        menuMgr.setRemoveAllWhenShown(true);
        menuMgr.addMenuListener(new IMenuListener() {
            public void menuAboutToShow(IMenuManager manager) {
                ProofVisualizationView.this.fillContextMenu(manager);
            }
        });
        Menu menu = menuMgr.createContextMenu(viewer.getControl());
        viewer.getControl().setMenu(menu);
        getSite().registerContextMenu(menuMgr, viewer);
    }

    private void contributeToActionBars() {
        IActionBars bars = getViewSite().getActionBars();
        fillLocalPullDown(bars.getMenuManager());
        fillLocalToolBar(bars.getToolBarManager());
    }

    private void fillLocalPullDown(IMenuManager manager) {
        manager.add(visualizeNodeAction);
        manager.add(new Separator());
        manager.add(rmAnnotationsAction);
    }

    private void fillContextMenu(IMenuManager manager) {
        manager.add(toNodeAction);
        drillDownAdapter.addNavigationActions(manager);
        // Other plug-ins can contribute there actions here
        manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
    }
    
    private void fillLocalToolBar(IToolBarManager manager) {
        manager.add(new Separator());
        manager.add(stepIntoAction);
        manager.add(new Separator());
        manager.add(stepOverAction);
        manager.add(new Separator());
        manager.add(markNodeAction);
        manager.add(new Separator());
        manager.add(rmAnnotationsAction);
        manager.add(new Separator());
        manager.add(visualizeNodeAction);
        manager.add(new Separator());
        drillDownAdapter.addNavigationActions(manager);
    }

    private int lineInfo(SourceElement se) {
	final PositionInfo pi = se.getPositionInfo();
        int line = pi.getStartPosition().getLine();
        // TODO line information of local variable declaration is
        // wrong. bug in recoder?
	
        if (se instanceof LocalVariableDeclaration) {
	    if (se.getEndPosition().getLine() > line) {
		line++;
	    }
        }	
	
        return line - 1;
    }
    
    private void makeVisible(TraceElement he){
    	ISourceViewer viewer = 
            getSourceViewer(he.getSrcElement().getPositionInfo().getFileName());
        if (viewer == null)
            return;
        int line = lineInfo(he.getSrcElement());

        int sl = 0;
        int s2 = 1;
        try{
            sl = viewer.getDocument().getLineOffset(line);
            s2 = viewer.getDocument().getLineLength(line);
        }catch (BadLocationException e) {
        }        
        viewer.revealRange(sl, s2);
    }
    
    
    private void visualize(ContextTraceElement start, ContextTraceElement end){
        ContextTraceElement currentHe=start;
        LinkedList reverse = new LinkedList();
        while (currentHe!=end){
            reverse.addFirst(currentHe);
            currentHe = currentHe.getNextExecuted();

        }
        if (currentHe!=TraceElement.END) 
            reverse.addFirst(currentHe);
        HashSet visualized = new HashSet();
        boolean last= true;
        Iterator it = reverse.iterator();
        ContextTraceElement cte=TraceElement.END;
        while(it.hasNext()){
            cte = (ContextTraceElement)it.next();
            if (!visualized.contains(cte.getSrcElement().getPositionInfo())){
                if (last) visualizeTraceElement(cte,true);
                else visualizeTraceElement(cte,false);
                last=false;
                visualized.add(cte.getSrcElement().getPositionInfo());
            }
        }
        if (cte!=TraceElement.END) 
            makeVisible(cte);
    }
    
    public ExecutionTraceModel getModelSelection(VisualizationModel model){
        ModelSelectionDialog dialog= new ModelSelectionDialog(
                ProofVisualizationPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow().getShell(),model);
        dialog.setTitle("Proof Visualization");
        dialog.setMessage("Select an execution trace");
        dialog.open();
        return (ExecutionTraceModel)(dialog.getResult()[0]);
    }
    

    private void makeActions() {
        visualizeNodeAction = new Action() {
            public void run() {

                ProofVisualization proofVis = Main.getInstance().mediator().visualizeProof();
                if (proofVis != null) {

                    if (proofVis.getVisualizationModel().getExecutionTraces().length == 0) {
                        showMessage("No program executed on the branch so far.");
                    } else {
                        visualizationModel = proofVis.getVisualizationModel();

                        if (visualizationModel.getExecutionTraces().length > 1) {
                            ExecutionTraceModel selection = getModelSelection(visualizationModel);
                            if (selection != null) {
                                trace = selection;
                                toNodeAction.setEnabled(true);
                            } else
                                trace = null;
                        } else {
                            toNodeAction.setEnabled(true);
                            trace = (visualizationModel.getExecutionTraces())[0];
                        }
                        removeAnnotionMarkers();
                        if (trace.getFirstContextTraceElement() != TraceElement.END) {
                            visualize(trace.getFirstContextTraceElement(),
                                    TraceElement.END);
                            setUpTree(trace.getFirstContextTraceElement());
                            viewer.setExpandedElements(trace.getPath(trace
                                    .getLastContextTraceElement()));
                            stepOverAction.setEnabled(true);
                            stepIntoAction.setEnabled(true);
                            markNodeAction.setEnabled(true);

                        }
                    }
                } else
                    showMessage("No Proof Loaded");
            }
        };
        visualizeNodeAction.setText("Show Execution Traces");
        visualizeNodeAction
                .setToolTipText("Shows the execution traces for the current selected node in the KeY-Prover");
        visualizeNodeAction.setImageDescriptor(ImageDescriptor.createFromFile(
                this.getClass(), "visualize.png"));
        visualizeNodeAction.setImageDescriptor(null);

        markNodeAction = new Action() {
            public void run() {
                ProofVisualization proofVis = Main.getInstance().mediator()
                        .visualizeProof();
                if (proofVis != null) {
                    removeAnnotionMarkers();
                    visualize(trace.getFirstContextTraceElement(),
                            TraceElement.END);
                } else
                    showMessage("No Proof Loaded");
            }
        };
        markNodeAction.setText("Mark All Statements");
        markNodeAction
                .setToolTipText("Marks all statements of the execution trace in the Java editor");
        markNodeAction.setImageDescriptor(null);

        toNodeAction = new Action() {
            public void run() {
                ISelection selection = viewer.getSelection();
                Object obj = ((IStructuredSelection) selection)
                        .getFirstElement();
                TraceElement he = (TraceElement) obj;
                Main.getInstance().mediator().getSelectionModel()
                        .setSelectedNode(he.node());
            }
        };
        toNodeAction.setText("Select associated Node");
        toNodeAction.setEnabled(false);
        toNodeAction
                .setToolTipText("Selects the the associated Node in the KeY-Prover");
        toNodeAction.setImageDescriptor(PlatformUI.getWorkbench()
                .getSharedImages().getImageDescriptor(
                        ISharedImages.IMG_DEF_VIEW));

        rmAnnotationsAction = new Action() {
            public void run() {
                removeAnnotionMarkers();
            }
        };
        rmAnnotationsAction.setText("Remove all Markers");
        rmAnnotationsAction
                .setToolTipText("Removes all Proof Visualizuation Markers in the Java Editor");
        rmAnnotationsAction.setImageDescriptor(PlatformUI.getWorkbench()
                .getSharedImages().getImageDescriptor(
                        ISharedImages.IMG_TOOL_DELETE));

        stepIntoAction = new Action() {
            public void run() {
                IStructuredSelection selection = (IStructuredSelection) viewer
                        .getSelection();
                for (Iterator iterator = selection.iterator(); iterator
                        .hasNext();) {
                    Object domain = iterator.next();
                    if (domain instanceof ContextTraceElement) {
                        ContextTraceElement cte = (ContextTraceElement) domain;
                        if (cte.getNextExecuted() != TraceElement.END) {
                            viewer.setSelection(new StructuredSelection(cte
                                    .getNextExecuted()));                           
                        }
                    }
                }
            }
        };
        stepIntoAction.setToolTipText("Marks the next executed statement");
        stepIntoAction
                .setImageDescriptor(getImageDescriptor("stepinto_co.gif"));

        stepOverAction = new Action() {
            public void run() {
                IStructuredSelection selection = (IStructuredSelection) viewer
                        .getSelection();
                for (Iterator iterator = selection.iterator(); iterator
                        .hasNext();) {
                    Object domain = iterator.next();
                    if (domain instanceof ParentContextTraceElement) {
                        ParentContextTraceElement pcte = (ParentContextTraceElement) domain;
                        if (pcte.stepOver() != TraceElement.END) {
                            viewer.setSelection(new StructuredSelection(pcte
                                    .stepOver()));
                        }
                    } else if (domain instanceof ContextTraceElement) {
                        ContextTraceElement cte = (ContextTraceElement) domain;
                        if (cte.getNextExecuted() != TraceElement.END) {
                            viewer.setSelection(new StructuredSelection(cte
                                    .getNextExecuted()));
                        }
                    }
                }
            }
        };
        stepOverAction
                .setToolTipText("Step Over: Marks the next executed statement and"
                        + " jumps over substatements and method calls");
        stepOverAction
                .setImageDescriptor(getImageDescriptor("stepover_co.gif"));
        doubleClickAction = new Action() {
            public void run() {
                ISelection selection = viewer.getSelection();
                Object obj = ((IStructuredSelection) selection)
                        .getFirstElement();
                ContextTraceElement cte = (ContextTraceElement) obj;
                removeAnnotionMarkers();
                visualize(trace.getFirstContextTraceElement(), cte);
            }
        };

        stepOverAction.setEnabled(false);
        stepIntoAction.setEnabled(false);
        markNodeAction.setEnabled(false);
    }


    
    
    
    private ImageDescriptor getImageDescriptor(String file) {
        ImageDescriptor image = null;
        try {
            String filename = "icons/" + file;
            Bundle bun = Platform.getBundle("ProofVisualization");
            IPath ip = new Path(filename);
            URL url = Platform.find(bun, ip);

            URL resolved = Platform.resolve(url);

            image = ImageDescriptor.createFromURL(resolved);
        } catch (Exception e) {
            e.printStackTrace();
        }
        return image;
    }
    
    
    
    
    private void hookDoubleClickAction() {
        viewer.addDoubleClickListener(new IDoubleClickListener() {
            public void doubleClick(DoubleClickEvent event) {
                doubleClickAction.run();
            }
        });
        
    }
    private void showMessage(String message) {
        MessageDialog.openInformation(
        viewer.getControl().getShell(),"Proof Visualization", message);
    }


    public void setUpTree(ContextTraceElement cte){
        invisibleRoot.setStepInto(cte);
        viewer.refresh();
    }
    
 
    public void removeAnnotionMarkers(){
    	Object[] viewers = sViewerList.toArray();
    	for(int i=0; i<viewers.length;i++){
    		ISourceViewer viewer = (ISourceViewer)viewers[i];  
    		if (viewer == null) continue;
                    Iterator iterator = viewer.getAnnotationModel().getAnnotationIterator();
    		while (iterator.hasNext()){
    			Annotation ann = (Annotation)iterator.next();
    			if (ann instanceof PVAnnotation)
    				viewer.getAnnotationModel().removeAnnotation(ann);
    		}
      	}
        sViewerList = new LinkedList();
    }
    
    
    
    public ISourceViewer getSourceViewer(String file){
        IWorkspaceRoot myWorkspaceRoot = ResourcesPlugin.getWorkspace().getRoot();

        // TODO find the eclipse project of  the  proof 
        
        // This is a workaround, but
        // findFilesforLocations does not work with linked folders. 
        // See Bug 128460 at https://bugs.eclipse.org/
        // Bug is fixed in Stable Build: 3.2M5a

        IFile[] f= myWorkspaceRoot.findFilesForLocation(new Path(file));//pr.getFile(file);
        ISourceViewer viewer = null;
        IWorkbench workbench = PlatformUI.getWorkbench();
        IWorkbenchPage page = workbench.getActiveWorkbenchWindow().getActivePage();
        try{
            IEditorPart ed = org.eclipse.ui.ide.IDE.openEditor(page, f[0]);
            viewer =(ISourceViewer)ed.getAdapter(ITextOperationTarget.class);
        } catch( Exception e){
            e.printStackTrace();
            return null;
        }
        return viewer;
    }
        
    public void visualizeTraceElement(ContextTraceElement cte, boolean last) {
        ISourceViewer viewer = getSourceViewer(cte.getSrcElement()
                .getPositionInfo().getFileName());
        if (viewer==null)
            return;
        if (!sViewerList.contains(viewer))
            sViewerList.add(viewer);

	int line = lineInfo(cte.getSrcElement());

        if (!last) {
            setAnnotationMarker(viewer, cte, getMessage(cte), MARKER, line);
        } else {
            setAnnotationMarker(viewer, cte, getMessage(cte), LAST_MARKER, line);

        }
        if (cte.getLabel() != null && (cte.getLabel().length() > 0)) {
            setAnnotationMarker(viewer, cte, cte.getLabel(), MARKER, line);
        }

        if (cte == trace.getLastContextTraceElement()
                && trace.uncaughtException())
            setAnnotationMarker(viewer, cte, "Uncaught Exception: "
                    + trace.getUncaughtException().getSrcElement(), EXC_MARKER,
                    line);

    }
    
    
    public void setAnnotationMarker(ISourceViewer viewer, ContextTraceElement he, 
            String message, String type, int line){
	 int s1 = 0;
	 int s2 = 1;
	 try {
	     s1 = viewer.getDocument().getLineOffset(line);
             s2 = viewer.getDocument().getLineLength(line);             
	 } catch (BadLocationException e) {
             e.printStackTrace();
	 }
         
	 viewer.getAnnotationModel().
             addAnnotation(new PVAnnotation(type,false,he,message),			
						   new Position(s1, s2));
         viewer.revealRange(s1, s2);
    }
    
    public String getMessage(ContextTraceElement he){
        String s = "";
        if (he.getParent().getSrcElement() instanceof LoopStatement){
            if (he.getNumberOfExecutions()>1)
                s += "Unwound: "+he.getNumberOfExecutions()+" times";
            else if  (he.getNumberOfExecutions()==1)
                s += "Unwound: "+he.getNumberOfExecutions()+" time";
        }
        return s;
    }
    
    
    
    /**
     * Passing the focus request to the viewer's control.
     */
    public void setFocus() {
           viewer.getControl().setFocus();
    }
        
}
