package visualdebugger.views;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.*;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IVariableBinding;
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
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ITextEditor;

import visualdebugger.astops.PositionFinder;
import visualdebugger.astops.Util;
import de.uka.ilkd.key.visualdebugger.*;

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

    private ICompilationUnit icunit;

    private LinkedList<Integer> positions;

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

                    WatchExpressionDialog dialog = new WatchExpressionDialog(shell, wpd);

                    if (wpd != null) {

                        WatchpointDescriptor result = dialog.open();
                        setPositions(dialog.getPositions());
                        
                        if (result.getExpression() != null) {
                            // create global watchpoint
                            if (!result.isLocal()) {
                                watchPointManager.addWatchPoint(new WatchPoint(
                                        result));
                            } // create watchpoint for local variable
                            else {
                                // TODO
                                WatchpointDescriptor includingLocalVariables = getLocalVariables(result);
                                if (includingLocalVariables != null)
                                    watchPointManager
                                            .addWatchPoint(new WatchPoint(
                                                    includingLocalVariables));
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
    //TODO move to Util class
    private WatchpointDescriptor getLocalVariables(WatchpointDescriptor wpd) {

        LinkedList<Integer> postions = getPositions();

        if (postions == null || postions.size() == 0)
            return wpd;
        assert(postions.size() > 0);
       
        CompilationUnit cu = Util.parse(getICUnit(), null);

        // get enumeration of the local variables
        PositionFinder pf  = new PositionFinder(wpd.getDeclaringMethod());
        pf.process(cu);
        
        HashMap<Integer, IVariableBinding> positionInfo = Util.valueToKey(pf.getPositionInfo());
        System.out.println(positionInfo);
        
        LinkedList<LocalVariableDescriptor> localVariables = new LinkedList<LocalVariableDescriptor>();
        Iterator<Integer> it = postions.iterator();
        while (it.hasNext()) {
            Integer pos = (Integer) it.next();
            IVariableBinding varBinding =  positionInfo.get(pos);
            localVariables.add(new LocalVariableDescriptor(varBinding.getName(),
                  varBinding.getType().getQualifiedName(), 0, pos, null));
        }   

        // reset method name :: this is important, otherwise KeY will not be able to find the method later on
        try {
            IMethod m = (IMethod)getICUnit().getElementAt(wpd.getColumn());
            wpd.setDeclaringMethod(m.getElementName());
        } catch (JavaModelException e) {
            e.printStackTrace();
        }
        wpd.setLocalVariables(localVariables);
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
            setICUnit(unit);
            
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
                    watchpointDescriptor.setDeclaringMethod("Field "
                            + je.getElementName());
                    watchpointDescriptor.setLine(1 + tsel.getEndLine());
                    watchpointDescriptor.setColumn(offset);
                    watchpointDescriptor.setDeclaringType(((IField) je)
                            .getDeclaringType().getFullyQualifiedName());
                    watchpointDescriptor.setSource(source);
                    watchpointDescriptor.setVarName(varName);
                    watchpointDescriptor.setLocal(false);

                    return watchpointDescriptor;
                } else {
                    if (je instanceof IMethod) {

                        IMethod method = (IMethod) je;

                        watchpointDescriptor = new WatchpointDescriptor();
                        watchpointDescriptor.setName(je.getElementName());
                        watchpointDescriptor.setDeclaringMethod(method
                                .getElementName());
                        watchpointDescriptor.setLine(1 + tsel.getEndLine());
                        watchpointDescriptor.setColumn(offset);
                        watchpointDescriptor.setDeclaringType(method
                                .getDeclaringType().getFullyQualifiedName());
                        watchpointDescriptor.setSource(source);
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

    private void setICUnit(ICompilationUnit unit) {
        this.icunit = unit;
    }

    private ICompilationUnit getICUnit() {
        return icunit;
    }
    private void setPositions(LinkedList<Integer> positions) {
        this.positions = positions;
    }
    private LinkedList<Integer> getPositions() {
        return this.positions;
    }
}