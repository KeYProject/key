package visualdebugger.views;

import java.util.LinkedList;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.*;
import org.eclipse.jdt.core.dom.*;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.*;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart; //import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ITextEditor;

import de.uka.ilkd.key.visualdebugger.*;
import visualdebugger.astops.Util;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.WatchPoint;
import de.uka.ilkd.key.visualdebugger.WatchPointManager;
import de.uka.ilkd.key.visualdebugger.WatchpointDescriptor;

/**
 * The Class WatchpointView.
 */
public class WatchpointView extends ViewPart {

    private CompilationUnit unit;

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

    private Set<SimpleName> localVariables;

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
                result = "" + wp.getStatement_line();
                break;
            case 3:
                result = wp.getDeclaringType();
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
    // private void fillContextMenu(IMenuManager manager) {
    // manager.add(addAction);
    // manager.add(removeAction);
    // // Other plug-ins can contribute there actions here
    // manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
    // }
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
        final WatchpointView wv = this;
        addAction = new Action() {
            private Shell shell = new Shell();

            public void run() {

                WatchpointDescriptor wpd = getWatchPointDescriptor();
                if (wpd == null) {
                    MessageDialog
                            .openError(PlatformUI.getWorkbench()
                                    .getActiveWorkbenchWindow().getShell(),
                                    "Adding WatchPoint",
                                    "Please select a constant, field or a local variable to observe.");
                } else {

                    WatchExpressionDialog dialog = new WatchExpressionDialog(
                            shell, wv, wpd.getLine(), wpd.getSource(), wpd
                                    .getName());

                    if (wpd != null) {

                        String expression = dialog.open();

                        if (expression != null) {
                            wpd.setExpression(expression);
                            // create global watchpoint
                            if (!wpd.isLocal()) {
                                watchPointManager.addWatchPoint(new WatchPoint(
                                        wpd));
                            } // create watchpoint for local variable
                            else {
                                // TODO
                                watchPointManager.addWatchPoint(new WatchPoint(
                                        getLocalVariables(wpd)));
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
                    ((WatchPoint) element).setEnabled(false);
                    viewer.refresh();

                }
            }
        };
        disableAction.setText("Disable");
        disableAction.setToolTipText("disable watchpoint");

    }

    public WatchpointDescriptor getLocalVariables(
            WatchpointDescriptor wpd) {

        CompilationUnit cu = getUnit();
        ASTNode astnode;

        LinkedList<LocalVariableDescriptor> locVariables = new LinkedList<LocalVariableDescriptor>();
        for (SimpleName simpleName : localVariables) {
            IVariableBinding varBinding = (IVariableBinding) simpleName
                    .resolveBinding();
            // FIXME pull out of loop
            // getting the method signature
            ITypeBinding[] itb = varBinding.getDeclaringMethod()
                    .getParameterTypes();
            LinkedList<String> ll = new LinkedList<String>();
            for (int i = 0; i < itb.length; i++) {
                ll.add(itb[i].getName());
            }
            wpd.setParameterTypes(ll);
            astnode = cu.findDeclaringNode(varBinding);
            int startPosition = astnode.getStartPosition();

            System.out.println(cu.getLineNumber(startPosition) + " : "
                    + cu.getColumnNumber(startPosition) +" >> "+varBinding.getType().getName() +" "+ varBinding.getName());

            locVariables.add(new LocalVariableDescriptor(varBinding.getName(),
                    varBinding.getType().getName(), cu
                            .getLineNumber(startPosition), cu
                            .getColumnNumber(startPosition), null));

        }
        wpd.setLocalVariables(locVariables);
        return wpd;

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

    // TODO correct the doc

    /**
     * Gets the watch point descriptor.
     * 
     * @return the watch point descriptor
     */
    private WatchpointDescriptor getWatchPointDescriptor() {

        WatchpointDescriptor watchpointDescriptor = null;
        String varName = "myDummy";

        IEditorPart editor = PlatformUI.getWorkbench()
                .getActiveWorkbenchWindow().getActivePage().getActiveEditor();
        if (editor instanceof ITextEditor) {
            ITextEditor tedit = (ITextEditor) editor;
            ISelection sel = tedit.getSelectionProvider().getSelection();
            ITextSelection tsel = (ITextSelection) sel;
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
                e.printStackTrace();
            }

            try {
                IJavaElement je = unit.getElementAt(offset);

                if (je instanceof IField) {
                    watchpointDescriptor = new WatchpointDescriptor();

                    watchpointDescriptor
                            .setName("Field " + je.getElementName());
                    watchpointDescriptor.setDeclaringMethod("Field " + je.getElementName());
                    watchpointDescriptor.setLine(1 + tsel.getEndLine());
                    watchpointDescriptor.setColumn(offset);
                    watchpointDescriptor.setDeclaringType(((IField) je)
                            .getDeclaringType().getFullyQualifiedName());
                    watchpointDescriptor.setSource(source);
                    //**
                    watchpointDescriptor.setVarName(varName);
                    watchpointDescriptor.setLocal(false);

                    return watchpointDescriptor;
                } else {
                    if (je instanceof IMethod) {

                        IMethod method = (IMethod) je;

                        watchpointDescriptor = new WatchpointDescriptor();
                        watchpointDescriptor.setName(je.getElementName());
                        watchpointDescriptor.setDeclaringMethod(method.getElementName());
                        watchpointDescriptor.setLine(1 + tsel.getEndLine());
                        watchpointDescriptor.setColumn(offset);
                        watchpointDescriptor.setDeclaringType(method
                                .getDeclaringType().getFullyQualifiedName());
                        watchpointDescriptor.setSource(source);
                        //**
                        watchpointDescriptor.setVarName(varName);
                        watchpointDescriptor.setLocal(true);

                        return watchpointDescriptor;

                    } else {
                        return null;
                    }
                }

            } catch (JavaModelException e) {
                e.printStackTrace();
            } catch (Throwable t) {
                t.printStackTrace();
            }
        }
        return watchpointDescriptor;
    }

    public void setLocalVariables(Set<SimpleName> localVariables) {
        this.localVariables = localVariables;
    }

    public CompilationUnit getUnit() {
        return unit;
    }

    public void setUnit(CompilationUnit unit) {
        this.unit = unit;
    }

}