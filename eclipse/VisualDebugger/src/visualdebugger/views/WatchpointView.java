package visualdebugger.views;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.*;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jface.action.*;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextOperationTarget;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.viewers.*;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.*;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.MarkerUtilities;

import de.uka.ilkd.key.visualdebugger.*;
import de.uka.ilkd.key.visualdebugger.executiontree.*;

/**
 * The Class WatchpointView.
 */
public class WatchpointView extends ViewPart {

    /** The viewer. */
    private TableViewer viewer;

    /** The delete action. */
    private Action deleteAction;

    /** The add action. */
    private Action addAction;

    /** The bp manager. */
    private BreakpointManager bpManager;

    /**
     * The Class BpContentProvider.
     */
    class BpContentProvider implements IStructuredContentProvider {

        /**
         * Input changed.
         * 
         * @param v
         *            the v
         * @param oldInput
         *            the old input
         * @param newInput
         *            the new input
         */
        public void inputChanged(Viewer v, Object oldInput, Object newInput) {
        }

        /**
         * Dispose.
         */
        public void dispose() {
        }

        /**
         * Gets the elements.
         * 
         * @param parent
         *            the parent
         * 
         * @return the elements
         */
        public Object[] getElements(Object parent) {
            if (parent instanceof BreakpointManager) {
                return ((BreakpointManager) parent).getBreapoints();
            } else
                return new String[] { "One", "Two", "Three" };
        }
    }

    /**
     * The Class BpLabelProvider.
     */
    class BpLabelProvider extends LabelProvider implements ITableLabelProvider {

        /**
         * Gets the column text.
         * 
         * @param obj
         *            the obj
         * @param index
         *            the index
         * 
         * @return the column text
         */
        public String getColumnText(Object obj, int index) {
            if (obj instanceof BreakpointEclipse) {
                BreakpointEclipse b = (BreakpointEclipse) obj;
                if (index == 2) {
                    final String s = b.getStatement().toString();
                    return s.substring(0, s.lastIndexOf("\n"));
                } else if (index == 0) {
                    return b.getCompilationUnit().getResource().getName();
                } else if (index == 1) {
                    return b.getMethod().getElementName();
                }

                return b.getId().getId() + "";
            }
            return "UNKNOWN CONTENT";
        }

        /**
         * Gets the column image.
         * 
         * @param obj
         *            the obj
         * @param index
         *            the index
         * 
         * @return the column image
         */
        public Image getColumnImage(Object obj, int index) {
            return null;
        }

        /**
         * Gets the image.
         * 
         * @param obj
         *            the obj
         * 
         * @return the image
         */
        public Image getImage(Object obj) {
            return PlatformUI.getWorkbench().getSharedImages().getImage(
                    ISharedImages.IMG_OBJ_ELEMENT);
        }
    }

    /**
     * Instantiates a new breakpoint view.
     */
    public WatchpointView() {
        bpManager = VisualDebugger.getVisualDebugger().getBpManager();
    }

    /**
     * This is a callback that will allow us to create the viewer and initialize
     * it.
     * 
     * @param parent
     *            the parent
     */
    public void createPartControl(Composite parent) {
        viewer = new TableViewer(parent, SWT.MULTI | SWT.H_SCROLL
                | SWT.V_SCROLL | SWT.SEPARATOR);

        // viewer.setSorter(new NameSorter());

        Table table = viewer.getTable();
        // table.setLayoutData(new GridData(GridData.FILL_BOTH));
        TableColumn column;

        column = new TableColumn(table, SWT.NONE, 0);
        column.setWidth(200);
        column.setText("Watch Expression");
        column = new TableColumn(table, SWT.NONE, 1);
        column.setWidth(100);
        column.setText("File");
        column = new TableColumn(table, SWT.NONE, 2);
        column.setWidth(100);
        column.setText("Method");
        column = new TableColumn(table, SWT.NONE, 3);
        column.setWidth(70);
        column.setText("Statement");
        table.setHeaderVisible(true);
        table.setLinesVisible(true);
        viewer.setContentProvider(new BpContentProvider());
        viewer.setLabelProvider(new BpLabelProvider());

        viewer.setInput(bpManager);

        hookListener();
        makeActions();
        hookContextMenu();

        contributeToActionBars();
    }

    /**
     * Hook listener.
     */
    private void hookListener() {
        viewer.addSelectionChangedListener(new ISelectionChangedListener() {
            public void selectionChanged(SelectionChangedEvent event) {
                // if the selection is empty clear the label
                if (event.getSelection().isEmpty()) {

                    return;
                }
                if (event.getSelection() instanceof IStructuredSelection) {
                    IStructuredSelection selection = (IStructuredSelection) event
                            .getSelection();

                    Object domain = selection.getFirstElement();
                    if (domain instanceof BreakpointEclipse) { // TODO !!!!!
                        BreakpointEclipse bp = (BreakpointEclipse) domain;
                        // ICompilationUnit unit = bp.getCompilationUnit();
                        ISourceViewer viewer = null;
                        IWorkbench workbench = PlatformUI.getWorkbench();
                        IWorkbenchPage page = workbench
                                .getActiveWorkbenchWindow().getActivePage();
                        IMarker marker = null;
                        // TODO add marker attribute to BreakpointEclipse
                        try {
                            IMarker[] markers = bp.getCompilationUnit()
                                    .getResource().findMarkers(
                                            "VisualDebugger.bpmarker", true, 1);
                            for (int i = 0; i < markers.length; i++) {

                                if (((Integer) markers[i]
                                        .getAttribute("StatementId"))
                                        .intValue() == bp.getId().getId()) {
                                    marker = markers[i];
                                }
                            }
                        } catch (CoreException e) {
                            // TODO Auto-generated catch block
                            e.printStackTrace();
                        }

                        try {
                            IEditorPart ed = org.eclipse.ui.ide.IDE.openEditor(
                                    page, marker, true);
                            viewer = (ISourceViewer) ed
                                    .getAdapter(ITextOperationTarget.class);
                        } catch (Exception e) {
                            e.printStackTrace();

                        }

                        // IEditorPart editor
                        // =PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
                        /*
                         * //bp.getAnnotation().getSourceViewer().setSelectedRange(bp.getSelection().getOffset(),
                         * bp.getSelection().getLength()); if (editor instanceof
                         * ITextEditor){ ITextEditor tedit= (ITextEditor)
                         * editor;
                         * tedit.getSelectionProvider().setSelection(bp.getSelection()); }
                         */

                    }
                }
            }
        });
    }

    /**
     * Hook context menu.
     */
    private void hookContextMenu() {
        MenuManager menuMgr = new MenuManager("#PopupMenu");
        menuMgr.setRemoveAllWhenShown(true);
        menuMgr.addMenuListener(new IMenuListener() {
            public void menuAboutToShow(IMenuManager manager) {
            	WatchpointView.this.fillContextMenu(manager);
            }
        });
        Menu menu = menuMgr.createContextMenu(viewer.getControl());
        viewer.getControl().setMenu(menu);
        getSite().registerContextMenu(menuMgr, viewer);
    }

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
        manager.add(new Separator());
        manager.add(deleteAction);
    }

    /**
     * Fill context menu.
     * 
     * @param manager
     *            the manager
     */
    private void fillContextMenu(IMenuManager manager) {
        manager.add(addAction);
        manager.add(deleteAction);
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
        manager.add(deleteAction);
    }

    /**
     * Make actions.
     */
    private void makeActions() {
        addAction = new Action() {
            public void run() {
                IEditorPart editor = PlatformUI.getWorkbench()
                        .getActiveWorkbenchWindow().getActivePage()
                        .getActiveEditor();
                if (editor instanceof ITextEditor) {
                    ITextEditor tedit = (ITextEditor) editor;

                    ISelection sel = tedit.getSelectionProvider()
                            .getSelection();
                    ITextSelection tsel = (ITextSelection) sel;
                    IFile file = (IFile) tedit.getEditorInput().getAdapter(
                            IFile.class);

                    String fileName = file.getProjectRelativePath().toString();
                    System.out.println(fileName);
                    System.out.println("FileName " + fileName);

                    ICompilationUnit unit = JavaCore
                            .createCompilationUnitFrom(file);
                    IMethod method = null;
                    try {
                        IJavaElement je = unit.getElementAt(tsel.getOffset());
                        if (je instanceof IMethod) {
                            method = (IMethod) je;
                        }

                        // System.out.println(method);
                        // System.out.println(method.getClass());
                    } catch (JavaModelException e) {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }

                    // -------- get File
                    IProject project = unit.getJavaProject().getProject();
                    File location = project.getLocation().toFile();
                    File f = new File(location + fileName);
                    System.out.println(location + "/" + fileName);
                    // ----------------------

                    ASTParser parser = ASTParser.newParser(AST.JLS3);
                    parser.setResolveBindings(true);
                    parser.setSource(unit);
                    CompilationUnit astRoot = (CompilationUnit) parser
                            .createAST(null);

                    FindStatementVisitor visitor = new FindStatementVisitor(
                            tsel.getOffset());
                    astRoot.accept(visitor);

                    if (visitor.getStatement() == null) {
                        MessageDialog
                                .openError(PlatformUI.getWorkbench()
                                        .getActiveWorkbenchWindow().getShell(),
                                        "Adding Statement Breakpoint",
                                        "Please select a Java statement in the Java Editor");
                        return;
                    }
                    // ISourceViewer sviewer = getSourceViewer(file);

                    // BreakpointAnnotation annotation = new
                    // BreakpointAnnotation("VisualDebugger.BpAnnotationType",true,"Statement
                    // Breakpoint",sviewer);
                    // new
                    // BreakpointAnnotation("VisualDebugger.BpAnnotationType",marker);
                    // System.out.println("P " +annotation.isPersistent());
                    BreakpointEclipse bp = new BreakpointEclipse(
                            new SourceElementId("", visitor.getStatementId()),
                            visitor.getTextSelection(), visitor.getStatement(),
                            unit, method);
                    if (!bpManager.addBreakpoint(bp))
                        return;
                    try {
                        Map map = new HashMap();
                        map.put("StatementId", new Integer(visitor
                                .getStatementId()));
                        // MarkerUtilities.setLineNumber(map, 10);
                        MarkerUtilities.setCharStart(map, visitor
                                .getTextSelection().getOffset());
                        MarkerUtilities.setCharEnd(map, visitor
                                .getTextSelection().getOffset()
                                + visitor.getTextSelection().getLength());

                        MarkerUtilities.createMarker(unit.getResource(), map,
                                "VisualDebugger.bpmarker");

                    } catch (CoreException e) {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }
                    // --------------------------------------------------------

                    // TODO start/end line
                    // IDocument doc =
                    // tedit.getDocumentProvider().getDocument(null);
                    // IRegion i =
                    // doc.getLineInformationOfOffset(bp.getSelection().getOffset());
                    // Line Tracker...

                    // sviewer.getAnnotationModel().
                    // addAnnotation(annotation,
                    // new Position(visitor.getTextSelection().getOffset(),
                    // visitor.getTextSelection().getLength()));
                    // sviewer.revealRange(visitor.getTextSelection().getOffset(),
                    // visitor.getTextSelection().getOffset());

                    viewer.setInput(bpManager);
                    DebuggerEvent event = new DebuggerEvent(
                            DebuggerEvent.TREE_CHANGED, ExecutionTree
                                    .getITNode());
                    VisualDebugger.getVisualDebugger().fireDebuggerEvent(event);

                }
            }
        };
        addAction.setText("Add");
        addAction.setToolTipText("Adds a statement breakpoint");
        // addAction.setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().
        // getImageDescriptor(ISharedImages.IMG_OBJ_FILE));

        deleteAction = new Action() {
            public void run() {
                IStructuredSelection sel = (IStructuredSelection) viewer
                        .getSelection();

                Object domain = sel.getFirstElement();
                if (domain instanceof BreakpointEclipse) {
                    BreakpointEclipse bp = (BreakpointEclipse) domain;
                    try {
                        IMarker[] markers = bp.getCompilationUnit()
                                .getResource().findMarkers(
                                        "VisualDebugger.bpmarker", true, 1);
                        for (int i = 0; i < markers.length; i++) {
                            if (((Integer) markers[i]
                                    .getAttribute("StatementId")).intValue() == bp
                                    .getId().getId()) {
                                markers[i].delete();
                            }
                        }
                    } catch (CoreException e) {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }

                    // ISourceViewer sviewer =
                    // bp.getAnnotation().getSourceViewer();
                    // sviewer.getAnnotationModel().removeAnnotation(bp.getAnnotation());
                    bpManager.remove(bp);
                    viewer.setInput(bpManager);
                    DebuggerEvent event = new DebuggerEvent(
                            DebuggerEvent.TREE_CHANGED, ExecutionTree
                                    .getITNode());
                    VisualDebugger.getVisualDebugger().fireDebuggerEvent(event);

                    // showMessage("Action 1 executed");

                }
            }
        };
        deleteAction.setText("Remove");
        deleteAction.setToolTipText("Removes the selected breakpoint");
        // deleteAction.setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().
        // getImageDescriptor(ISharedImages.IMG_TOOL_DELETE));

    }

    /**
     * Passing the focus request to the viewer's control.
     */
    public void setFocus() {
        viewer.getControl().setFocus();
    }
}