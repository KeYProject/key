package visualdebugger.views;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import visualdebugger.astops.*;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ITextEditor;

import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.WatchPoint;
import de.uka.ilkd.key.visualdebugger.WatchPointManager;

/**
 * The Class WatchpointView.
 */
public class WatchpointView extends ViewPart {

    /** The viewer. */
    private TableViewer viewer;

    /** The delete action. */
    private Action removeAction;

    /** The add action. */
    private Action addAction;

    /** The watch point manager. */
    private WatchPointManager watchPointManager;

    private VisualDebugger vd = null;

    private Action disableAction;

    private Action enableAction;

    /**
     * The Class WatchPointContentProvider.
     */
    class WatchPointContentProvider implements IStructuredContentProvider {

        /*
         * (non-Javadoc)
         * 
         * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
         */
        public Object[] getElements(Object inputElement) {

            WatchPointManager wpm = (WatchPointManager) inputElement;
            return wpm.getWatchPointsAsArray();
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.eclipse.jface.viewers.IContentProvider#dispose()
         */
        public void dispose() {
            // TODO Auto-generated method stub

        }

        /*
         * (non-Javadoc)
         * 
         * @see org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface.viewers.Viewer,
         *      java.lang.Object, java.lang.Object)
         */
        public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
            // TODO Auto-generated method stub

        }

    }

    /**
     * The Class WatchPointLabelProvider.
     */
    class WatchPointLabelProvider extends LabelProvider implements
            ITableLabelProvider {

        /*
         * (non-Javadoc)
         * 
         * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnImage(java.lang.Object,
         *      int)
         */
        public Image getColumnImage(Object element, int columnIndex) {
            // TODO Auto-generated method stub
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnText(java.lang.Object,
         *      int)
         */
        public String getColumnText(Object element, int columnIndex) {
            String result = "";
            WatchPoint wp = (WatchPoint) element;
            switch (columnIndex) {
            case 0:
                result = wp.getExpression();
                break;
            case 1:
                result = wp.getMethod();
                break;
            case 2:
                result = wp.getStatement_line();
                break;
            case 3:
                result = wp.getTypeOfSource();
                break;
            case 4:
                result = "" + wp.isEnabled();
                break;
            default:
                break;
            }
            return result;
        }

    }

    /**
     * Instantiates a new breakpoint view.
     */
    public WatchpointView() {
        vd = VisualDebugger.getVisualDebugger();
        watchPointManager = vd.getWatchPointManager();
    }

    /**
     * This is a callback that will allow us to create the viewer and initialize
     * it.
     * 
     * @param parent
     *            the parent
     */
    public void createPartControl(Composite parent) {

        watchPointManager = vd.getWatchPointManager();
        viewer = new TableViewer(parent, SWT.MULTI | SWT.H_SCROLL
                | SWT.V_SCROLL | SWT.SEPARATOR);

        Table table = createTable();
        table.setHeaderVisible(true);
        table.setLinesVisible(true);

        viewer.setContentProvider(new WatchPointContentProvider());
        viewer.setLabelProvider(new WatchPointLabelProvider());

        viewer.setInput(watchPointManager);

        makeActions();
        // hookContextMenu();

        contributeToActionBars();
    }

    /**
     * Creates the table.
     * 
     * @return the table
     */
    private Table createTable() {
        Table table = viewer.getTable();

        TableColumn column;

        column = new TableColumn(table, SWT.NONE, 0);
        column.setWidth(150);
        column.setText("Watch Expression");

        column = new TableColumn(table, SWT.NONE, 1);
        column.setWidth(150);
        column.setText("Method");

        column = new TableColumn(table, SWT.NONE, 2);
        column.setWidth(100);
        column.setText("Line");

        column = new TableColumn(table, SWT.NONE, 3);
        column.setWidth(200);
        column.setText("Type");

        column = new TableColumn(table, SWT.NONE, 4);
        column.setWidth(80);
        column.setText("Enabled");
        return table;
    }

    /**
     * Hook context menu.
     */
    /*
     * private void hookContextMenu() { MenuManager menuMgr = new
     * MenuManager("#PopupMenu"); menuMgr.setRemoveAllWhenShown(true);
     * menuMgr.addMenuListener(new IMenuListener() { public void
     * menuAboutToShow(IMenuManager manager) {
     * WatchpointView.this.fillContextMenu(manager); } }); Menu menu =
     * menuMgr.createContextMenu(viewer.getControl());
     * viewer.getControl().setMenu(menu); getSite().registerContextMenu(menuMgr,
     * viewer); }
     */

    /**
     * Contribute to action bars.
     */
    private void contributeToActionBars() {
        IActionBars bars = getViewSite().getActionBars();
        fillLocalPullDown(bars.getMenuManager());
        fillLocalToolBar(bars.getToolBarManager());
    }

    /**
     * Fill local pull down.
     * 
     * @param manager
     *            the manager
     */
    private void fillLocalPullDown(IMenuManager manager) {

        manager.add(addAction);
        manager.add(removeAction);
        manager.add(new Separator());
        manager.add(disableAction);
        manager.add(enableAction);
    }

    /**
     * Fill context menu.
     * 
     * @param manager
     *            the manager
     */
    private void fillContextMenu(IMenuManager manager) {
        manager.add(addAction);
        manager.add(removeAction);
        // Other plug-ins can contribute there actions here
        manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
    }

    /**
     * Fill local tool bar.
     * 
     * @param manager
     *            the manager
     */
    private void fillLocalToolBar(IToolBarManager manager) {
        manager.add(addAction);
        manager.add(removeAction);

    }

    /**
     * Make actions.
     */
    private void makeActions() {
        addAction = new Action() {
            private Shell shell = new Shell();

            public void run() {

                String[] information = getWatchPointInf();
                if (information == null) {
                    MessageDialog
                            .openError(PlatformUI.getWorkbench()
                                    .getActiveWorkbenchWindow().getShell(),
                                    "Adding WatchPoint",
                                    "Please select a constant, field or a local variable declaration to observe.");
                } else {
                    WatchExpressionDialog dialog = new WatchExpressionDialog(
                            shell, java.lang.Integer.parseInt(information[1]),
                            information[3], information[0]);
                    if (information != null) {

                        String expression = dialog.open();

                        if (expression != null) {
                            // create global watchpoint
                            if(information.length==5){
                            watchPointManager.addWatchPoint(new WatchPoint(
                                    information[4], expression, information[0],
                                    information[1], information[2]));
                            } // create watchpoint for local variable
                            else{
                                int offset = Integer.parseInt(information[7]); 
                                watchPointManager.addWatchPoint(new WatchPoint(
                                        information[4], expression, information[6],
                                        information[1], information[2],information[5],information[6],offset));
                            }
                            vd.setWatchPointManager(watchPointManager);
                            viewer.refresh();
                        }
                    }
                }

            }

        };
        addAction.setText("Add");
        addAction.setToolTipText("Adds an expression that should be watched");

        removeAction = new Action() {
            public void run() {

                IStructuredSelection sel = (IStructuredSelection) viewer
                        .getSelection();

                Object element = sel.getFirstElement();
                if (element instanceof WatchPoint) {

                    watchPointManager.removeWatchPoint((WatchPoint) element);
                    viewer.refresh();

                }
            }
        };
        removeAction.setText("Remove");
        removeAction.setToolTipText("remove watchpoint");

        enableAction = new Action() {
            public void run() {

                IStructuredSelection sel = (IStructuredSelection) viewer
                        .getSelection();

                Object element = sel.getFirstElement();
                if (element instanceof WatchPoint) {
                    // TODO
                    ((WatchPoint) element).setEnabled(true);
                    viewer.refresh();

                }
            }
        };
        enableAction.setText("Enable");
        enableAction.setToolTipText("enable watchpoint");

        disableAction = new Action() {
            public void run() {

                IStructuredSelection sel = (IStructuredSelection) viewer
                        .getSelection();

                Object element = sel.getFirstElement();
                if (element instanceof WatchPoint) {
                    // TODO
                    ((WatchPoint) element).setEnabled(false);
                    viewer.refresh();

                }
            }
        };
        disableAction.setText("Disable");
        disableAction.setToolTipText("disable watchpoint");

    }

    /**
     * Passing the focus request to the viewer's control.
     */
    public void setFocus() {
        viewer.getControl().setFocus();
    }

    /**
     * Gets the watch point manager.
     * 
     * @return the watch point manager
     */
    public WatchPointManager getWatchPointManager() {
        return watchPointManager;
    }

    /**
     * Gets the WatchPoint information.
     * 
     * Collects the necessary information to create a watchpoint.
     * 
     * @return information where<br>
     * 
     * information[0]= The name of the JavaElement where the WatchPoint was set.<br>
     * information[1]= The line where the text selection ends. <br>
     * information[2]= The type in which the WatchPoint was set (fully qualified name).<br> 
     * information[3]= The actual the source code for validating the WatchPoint. <br>
     * information[4]= The unique name of the boolean variable that is used to validate the watchpoint.<br>
     ****** information[5] - [7] are only set for watchpoints on local variables.<br>
     * information[5] = The type of the local variable.<br>
     * information[6] = The name of the local variable.<br>
     * information[7] = The offset of the local variable.
     */
    private String[] getWatchPointInf() {

        String[] information = null;
        String varName = "myDummy";

        IEditorPart editor = PlatformUI.getWorkbench()
                .getActiveWorkbenchWindow().getActivePage().getActiveEditor();

        if (editor instanceof ITextEditor) {
            ITextEditor tedit = (ITextEditor) editor;

            ISelection sel = tedit.getSelectionProvider().getSelection();
            ITextSelection tsel = (ITextSelection) sel;
            // set current line

            int offset = tsel.getOffset();
            IFile file = (IFile) tedit.getEditorInput().getAdapter(IFile.class);

            ICompilationUnit unit = JavaCore.createCompilationUnitFrom(file);
            String source = "";

            try {
                source = unit.getBuffer().getContents();
                while (source.indexOf(varName) > (-1)) {
                    varName = varName.concat("x");
                }

            } catch (JavaModelException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

            try {
                IJavaElement je = unit.getElementAt(offset);

                if (je instanceof IField) {
                    information = new String[5];
                    information[0] = "Field " + je.getElementName();
                    information[1] = (1 + tsel.getEndLine()) + "";
                    information[2] = ((IField) je).getDeclaringType().getFullyQualifiedName();
                    information[3] = source;
                    information[4] = varName;

                    return information;
                } else {
                    if (je instanceof IMethod) {

                        IMethod method = (IMethod) je;

                        final String methodName = method.getElementName();

                        LocalVariableDetector localVariableDetector = new LocalVariableDetector();
                        CompilationUnit cu = parse(unit);
                        localVariableDetector.process(cu);
                        Map<IVariableBinding, VariableBindingManager> localVariableManagers = localVariableDetector
                                .getLocalVariableManagers();
                        Set<IVariableBinding> s = localVariableManagers
                                .keySet();

                        for (Iterator<IVariableBinding> iterator = s.iterator(); iterator
                                .hasNext();) {
                            IVariableBinding variableBinding = (IVariableBinding) iterator
                                    .next();

                            if (methodName.equals(variableBinding
                                    .getDeclaringMethod().getName())) {

                                ASTNode astnode = cu
                                        .findDeclaringNode(variableBinding);

                                if (isSelected(astnode, offset)) {
                                    information = new String[8];
                                    
                                    information[0] = variableBinding.getJavaElement().getElementName()+"";
                                    information[1] = (1 + tsel.getEndLine()) + "";
                                    information[2] = method.getDeclaringType().getFullyQualifiedName();
                                    information[3] = source;
                                    information[4] = varName;
                                    information[5] = variableBinding.getType().getName()+"";
                                 // alternative would be information[7] = methodName; -> returns only the name, no signature
                                    information[6] = variableBinding.getDeclaringMethod()+"";
                                    information[7] = astnode.getStartPosition()+"";

                                    return information; 
                                }
                            }
                        }
                    } else {
                        return null;
                    }
                }

            } catch (JavaModelException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        return information;
    }

    private boolean isSelected(ASTNode astnode, int offset) {
        int startposition = astnode.getStartPosition();
        int endposition = startposition + astnode.getLength();
        return (startposition <= offset && offset <= endposition);
    }

    protected CompilationUnit parse(ICompilationUnit lwUnit) {
        ASTParser parser = ASTParser.newParser(AST.JLS3);
        parser.setKind(ASTParser.K_COMPILATION_UNIT);
        parser.setSource(lwUnit); 
        parser.setResolveBindings(true);
        return (CompilationUnit) parser.createAST(null /* IProgressMonitor */);
    }
}