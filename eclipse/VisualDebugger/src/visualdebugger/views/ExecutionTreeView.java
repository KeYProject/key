package visualdebugger.views;

import java.util.*;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.draw2d.*;
import org.eclipse.draw2d.Label;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextOperationTarget;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowData;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.*;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.MarkerUtilities;

import visualdebugger.Activator;
import visualdebugger.VBTBuilder;
import visualdebugger.draw2d.*;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.smt.RuleLauncher;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.unittest.ModelGenerator;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.key.visualdebugger.DebuggerEvent;
import de.uka.ilkd.key.visualdebugger.DebuggerListener;
import de.uka.ilkd.key.visualdebugger.SourceElementId;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.executiontree.*;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchPoint;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchpointUtil;

// TODO: Auto-generated Javadoc

/**
 * The Class ExecutionTreeView.
 */
public class ExecutionTreeView extends ViewPart implements DebuggerListener {

    /** The Constant debug. */
    private static final boolean debug = false;

    /** The bc labels. */
    private boolean bcLabels = true;

    /** The bc list control. */
    private List bcListControl;

    /** The class menu. */
    Menu classMenu;

    /** The current root. */
    ITNode currentRoot = null;

    /**
     * The currentETRootNode. Used to keep track of the rootNode in the View.
     * This one is independent from the model and just for displaying purposes.
     */
    ETNode currentETRootNode = null;

    /** The cut tree. */
    private boolean cutTree = false;

    /** The figure canvas. */
    FigureCanvas figureCanvas;

    /** The hide infeasible. */
    boolean hideInfeasible = true;

    /** The labels. */
    HashSet labels = new HashSet();

    /** The LightweightSystem of Draw2D. */
    LightweightSystem lws;

    /** The maxmerge. */
    int maxmerge = 0;

    /** The merged. */
    int merged = 0;

    /** The mslet action. */
    private Action msletAction;

    /** The parent. */
    Composite parent;

    /** The root. */
    TreeRoot root;

    /** The selected. */
    private Figure selected;

    /** The selected min. */
    private MethodInvocationFigure selectedMIN = null;

    /** The shell. */
    Shell shell;

    /** The progress bar1. */
    private ProgressBar progressBar1;

    /** The slet action. */
    private Action sletAction;

    /** The decision procedure action. */
    private Action testCaseAction, decisionProcedureAction;

    /** The unit of last exception marker. */
    private ICompilationUnit unitOfLastExceptionMarker = null;

    /** The use branch labels action. */
    private Action useBranchLabelsAction;

    /** The VisualDebugger. */
    final VisualDebugger vd;

    /** The branch condition text. */
    Text bcText;

    /** The progress group. */
    private Label progressGroup;

    /** The item all. */
    private MenuItem itemAll;

    /** The item isolated. */
    private MenuItem itemIsolated;

    /** The collapse filter. */
    private CollapseFilter collapseFilter;
    private BranchFilter branchFilter;
    
    private Filter activeFilter = new TreeFilter();

    /** The item expand. */
    private MenuItem itemExpand;

    /** The clear view action. */
    private Action clearViewAction;

    /** The recompute watchpoints. */
    private Action recomputeWatchpoints;

    private List wpInfo;

    private Action clearWatchpoints;

    /**
     * Instantiates a new execution tree view.
     */
    public ExecutionTreeView() {
        vd = VisualDebugger.getVisualDebugger();
        vd.addListener(this);
    }

    /**
     * Builds the raw tree.
     * 
     * @param n
     *            the n
     * 
     * @return the tree branch
     */
    public synchronized TreeBranch buildRawTree(ITNode n) {
        SourceElementFigure statementNode = createNode("Node: " + n.getId()
                + "\n" + n.getActStatement(), true);
        TreeBranch branch = new TreeBranch(statementNode, null);

        ITNode[] children = n.getChildren();
        if (children != null && children.length > 0) {
            for (int i = 0; i < children.length; i++) {
                TreeBranch subTree = buildRawTree(children[i]);
                branch.addBranch(subTree, children[i].getBc() + "");
                root.addLabel(createConnection(statementNode,
                        subTree.getNode(), children[i].getBc() != null ? vd
                                .prettyPrint(children[i].getBc()) : "NULL",
                        true));
            }
        }
        return branch;
    }

    /**
     * Builds the tree branch.
     * 
     * This function builds the ExecutionTree in the View. It draws the passed
     * ETNode according to its type by calling createNode(ETNode). For every
     * child of this node the function is called recursively. On the return from
     * the calls the connections between the nodes are painted.
     * 
     * You can specify a Filter to display only certain nodes. The basic type is
     * TreeFilter which displays every node. BranchFilter are used to isolate a
     * certain path.
     * 
     * @param etn
     *            the ETNode
     * @param parent
     *            the parent
     * @param f
     *            the f
     * 
     * @return the tree branch
     */
    public synchronized TreeBranch buildTreeBranch(ETNode etn,
            TreeBranch parent, Filter f) {

        try {
            // draw node n
            IFigure statementNode = createNode(etn);
            // attach MouseListner
            statementNode.addMouseListener(new MouseListener.Stub() {
                public void mousePressed(MouseEvent event) {
                    if (event.button == 3) {
                        classMenu.setVisible(true);
                    }
                }
            });

            createRighClickContextMenu();

            TreeBranch branch = new TreeBranch(statementNode, parent);
            ETNode[] children = etn.getChildren();

            if (children != null && children.length > 0) {

                for (int i = 0; i < children.length; i++) {

                    TreeBranch subTree = null;

                    // display only the children that pass the filter
                    if (f.filter(children[i])) {
                        subTree = buildTreeBranch(children[i], branch, f);
                        branch.addBranch(subTree, children[i].getBC() + "");

                        final Connection c = createConnection(statementNode,
                                subTree.getNode(),
                                children[i].getBC() != null ? vd
                                        .prettyPrint(children[i]
                                                .getSimplifiedBc()) : "NO BC",
                                (children.length > 1));
                        subTree.setConnection(c);

                        // c.setForegroundColor(ColorConstants.red);
                        root.addLabel(c);
                        // }
                    }
                }
            }
            return branch;
        } catch (OutOfMemoryError oome) {
            System.out.println("OUT OF MEMORY ERROR!!!");
        } catch (Throwable t) {
            System.out.println(t.toString());
            t.printStackTrace();
        }
        return null;
    }

    /**
     * Identify watchpoints.
     * 
     * @param nodesToEvaluate
     *            the ETNode
     */
    private void identifyWatchpoints(LinkedList<ETNode> nodesToEvaluate) {
// FIXME: create getter/setter for watchpoints to avoid translation overhead
        LinkedList<WatchPoint> watchpoints = vd.getWatchPointManager()
                .getListOfWatchpoints(vd.getMediator().getServices());
        if (!watchpoints.isEmpty()) {
            WatchpointUtil.setActiveWatchpoint(nodesToEvaluate, watchpoints);
        }
    }

    /**
     * Contribute to action bars.
     */
    private void contributeToActionBars() {
        IActionBars bars = getViewSite().getActionBars();
        // fillLocalPullDown(bars.getMenuManager());
        fillLocalToolBar(bars.getToolBarManager());
    }

    /**
     * Creates the connection.
     * 
     * @param figFrom
     *            the fig from
     * @param figTo
     *            the fig to
     * @param text
     *            the text
     * @param withLabel
     *            the with label
     * 
     * @return the connection
     */
    private Connection createConnection(IFigure figFrom, IFigure figTo,
            String text, boolean withLabel) {
        PolylineConnection con = new PolylineConnection();
        con.setSourceAnchor(new ChopboxAnchor(figFrom));
        con.setTargetAnchor(new ChopboxAnchor(figTo));
        PolygonDecoration decoration = new PolygonDecoration();
        decoration.setTemplate(PolygonDecoration.TRIANGLE_TIP);
        con.setTargetDecoration(decoration);

        Ellipse e = new Ellipse();

        Label label;
        if (text.length() < 20)
            label = new Label(text);
        else
            label = new Label(text.substring(0, 19) + "...");

        Font font = new Font(shell.getDisplay(), "Arial", 8, SWT.NORMAL);
        ;
        label.setFont(font);
        label.setToolTip(new Label(text));

        label.setText("BC");
        label.setOpaque(true);
        e.setToolTip(new Label(text));
        e.add(label);
        e.setOpaque(false);
        e.setPreferredSize(15, 15);
        // e.setSize(15, 15);
        if (!text.equals("NO BC") && withLabel)
            con.add(label, new MidpointLocator(con, 0));
        labels.add(label);
        return con;
    }

    /**
     * Creates the node.
     * 
     * This method draws the passed ETNode according to its specific type.
     * 
     * @param etNode
     *            the et node
     * 
     * @return the figure
     */
    private Figure createNode(ETNode etNode) {
        final java.util.List<WatchPoint> activeWPs = etNode.getWatchpointsSatisfied();
        final java.util.List<WatchPoint> watchpointsTrueInSubset =etNode.getWatchpointsSatisfied();
        if (etNode instanceof ETStatementNode) {
            final SourceElementFigure node = new SourceElementFigure(
                    (ETStatementNode) etNode);

            node.addMouseListener(new MouseListener.Stub() {
                public void mouseDoubleClicked(MouseEvent me) {
                    doubleClick(node);
                }

                public void mousePressed(MouseEvent me) {
                    setSelected(node);
                    wpInfo.removeAll();
                    //TODO extract method
                    try {
                        if (activeWPs != null && activeWPs.size()>0) {
                            for (WatchPoint watchpoint : activeWPs) {
                                if(watchpoint.testPossible()){
                                    wpInfo.add(watchpoint.getExpression() +" is possible@" + watchpoint.getMethod());
                                }else
                                wpInfo.add(watchpoint.getExpression() +"@" + watchpoint.getMethod());

                            }
                        } else {
                            if(watchpointsTrueInSubset != null && watchpointsTrueInSubset.size()>0){
                                for (WatchPoint wp : watchpointsTrueInSubset) {
                                    wpInfo.add("true in subset: " +wp.getExpression() +"@" + wp.getMethod());
                                }
                               
                            }
                        }
                    } catch (Throwable t) {
                        System.out.println(t.toString());
                    }
                }
            });
            return node;

        } else if (etNode instanceof ETLeafNode) {
            final ETLeafNode ln = (ETLeafNode) etNode;
            final LeafNode node = new LeafNode(ln);
            node.addMouseListener(new MouseListener.Stub() {
                public void mouseDoubleClicked(MouseEvent me) {
                    // doubleClick(node);
                }

                public void mousePressed(MouseEvent me) {
                    setLeafNodeSelected(node);
                }
            });

            return node;
        } else if (etNode instanceof ETMethodInvocationNode) {

            // if (true)
            // return new Label("TEST");

            final MethodInvocationFigure node = new MethodInvocationFigure(
                    (ETMethodInvocationNode) etNode);

            node.addMouseListener(new MouseListener.Stub() {
                public void mouseDoubleClicked(MouseEvent me) {
                    // doubleClick(node);
                }

                public void mousePressed(MouseEvent me) {
                    // setSelected(node);
                }
            });
            return node;

        }

        else if (etNode instanceof ETMethodReturnNode) {

            final MethodReturnFigure node = new MethodReturnFigure(
                    (ETMethodReturnNode) etNode);

            node.addMouseListener(new MouseListener.Stub() {
                public void mouseDoubleClicked(MouseEvent me) {
                    // doubleClick(node);
                }

                public void mousePressed(MouseEvent me) {
                    setSelected(node);
                }
            });
            return node;
        }
        // only visible for debug = true && statement level ET 2
        else {
            final Ellipse node = new Ellipse();
            node.setPreferredSize(10, 10);
            if (etNode.isNobc())
                node.setBackgroundColor(ColorConstants.yellow);
            else
                node.setBackgroundColor(ColorConstants.blue);
            // node.setMinimumSize(10, 10);
            return node;

        }

    }

    /**
     * Creates the node.
     * 
     * @param title
     *            the title
     * @param listener
     *            the listener
     * 
     * @return the source element figure
     */
    private SourceElementFigure createNode(String title, boolean listener) {

        final SourceElementFigure node = new SourceElementFigure(title);
        if (listener)
            node.addMouseListener(new MouseListener.Stub() {
                public void mouseDoubleClicked(MouseEvent me) {
                    // doExpandCollapse();
                }

                public void mousePressed(MouseEvent me) {
                    setSelected(node);
                }
            });

        if (!listener)
            node.setBackgroundColor(ColorConstants.white);
        return node;
    }

    /**
     * This is a callback that will allow us to create the viewer and initialize
     * it.
     * 
     * @param parent
     *            the parent
     */
    public void createPartControl(Composite parent) {
        shell = parent.getShell();

        // Put the LWS on the newly created Canvas.
        lws = new LightweightSystem(shell);

        this.parent = parent;

        // create left side of the view window
        parent.setLayout(new GridLayout(2, false));
        figureCanvas = new FigureCanvas(parent, SWT.NONE);
        figureCanvas.setScrollBarVisibility(FigureCanvas.AUTOMATIC);

        figureCanvas.getViewport().setContentsTracksHeight(true);
        figureCanvas.getViewport().setContentsTracksWidth(true);

        figureCanvas.setLayoutData(new GridData(GridData.FILL_BOTH));
        // create right side of the view window
        hookShell();
        // Create "Start" Node
        root = new TreeRoot(createNode("Start", false));
        root.setMajorSpacing(40);
        root.setMinorSpacing(30);

        figureCanvas.setContents(root);
        shell.redraw();

        shell.open();

        makeActions();
        // hookContextMenu();
        // hookDoubleClickAction();
        contributeToActionBars();
        collapseFilter = new CollapseFilter();

        if (vd.getCurrentTree() != null) {
            this.currentRoot = vd.getCurrentTree();
            this.refresh();
        }
    }

    /**
     * Creates the righ click context menu.
     */
    private void createRighClickContextMenu() {
        classMenu = new Menu(shell, SWT.POP_UP);
        // create run menu item
        MenuItem item = new MenuItem(classMenu, SWT.PUSH);
        item.setText("Run");
        item.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {

                collapseFilter.clear();
                // make sure that all information available is contained in the
                // root node
                currentETRootNode = null;
                final ImmutableList<Goal> goals = getSubtreeGoalsForETNode(((SourceElementFigure) ExecutionTreeView.this.selected)
                        .getETNode());
                vd.run(goals);
            }

        });

        // create Step into button
        item = new MenuItem(classMenu, SWT.PUSH);
        item.setText("Step Into");
        item.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {
                ETNode node = ((SourceElementFigure) ExecutionTreeView.this.selected)
                        .getETNode();
                final ImmutableList<Goal> goals = getSubtreeGoalsForETNode(node);
                vd.stepInto(goals);
            }
        });

        // create Step Over button
        item = new MenuItem(classMenu, SWT.PUSH);
        item.setText("Step Over");
        item.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {
                final ImmutableList<Goal> goals = getSubtreeGoalsForETNode(((SourceElementFigure) ExecutionTreeView.this.selected)
                        .getETNode());
                vd.stepOver(goals);
            }
        });
        // create visualize button
        item = new MenuItem(classMenu, SWT.PUSH);
        item.setText("Visualize Node");
        item.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {
                vd
                        .visualize(((SourceElementFigure) ExecutionTreeView.this.selected)
                                .getETNode().getITNodesArray()[0]);

            }

        });
        // create Step into button
        item = new MenuItem(classMenu, SWT.PUSH);
        item.setText("Evaluate Watchpoints for Node");
        item.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {
                ETNode etn = ((SourceElementFigure) ExecutionTreeView.this.selected)
                        .getETNode();
                LinkedList<ETNode> node = new LinkedList<ETNode>();
                node.add(etn);
                try {
                    currentETRootNode = null;
                    identifyWatchpoints(node);     
                    clearView();
                    TreeBranch tb = buildTreeBranch(
                            getCurrentETRootNode(), null,
                            activeFilter);
                    root.addBranch(tb);
                    sketchStartUpConnection(tb);
                }
                catch (Throwable t){
                    System.out.println(t.toString());
                    
                }
            }
        });
        item = new MenuItem(classMenu, SWT.SEPARATOR);

        // create Step Over button
        item = new MenuItem(classMenu, SWT.PUSH);
        item.setText("Set Node to Root");
        item.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {

                // clear the View
                clearView();
                currentETRootNode = getSelectedNode();

                // set the current node as root
                TreeBranch treeBranch = buildTreeBranch(getSelectedNode(),
                        null, collapseFilter);
                root.addBranch(treeBranch);
                sketchStartUpConnection(treeBranch);
                // handle menu status
                itemAll.setEnabled(true);
                itemExpand.setEnabled(true);
            }
        });
        // collapse tree below
        item = new MenuItem(classMenu, SWT.PUSH);
        item.setText("Collapse Node");
        item.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {

                // make sure that there is a root node
                // save the actual root
                setCurrentETRootNode(currentETRootNode);
                collapseFilter.addNodetoCollapse(getSelectedNode());

                // clear the View
                clearView();
                TreeBranch tb = buildTreeBranch(getCurrentETRootNode(), null,
                        collapseFilter);

                // draw the new view of the tree
                root.addBranch(tb);
                // refresh();
                sketchStartUpConnection(tb);
                activeFilter=collapseFilter;
                // handle menu status
                itemAll.setEnabled(true);
                itemExpand.setEnabled(true);

            }

        });

        // expand current node
        itemExpand = new MenuItem(classMenu, SWT.PUSH);
        itemExpand.setText("Expand Node");
        itemExpand.setEnabled(false);
        itemExpand.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {

                // make sure that there is a root node
                currentETRootNode = getCurrentETRootNode();
                // save the actual root
                setCurrentETRootNode(currentETRootNode);
                collapseFilter.removeNodetoCollapse(getSelectedNode());
                // clear the View
                clearView();
                TreeBranch tb = buildTreeBranch(currentETRootNode, null,
                        collapseFilter);

                // draw the new view of the tree
                root.addBranch(tb);
                // refresh();
                sketchStartUpConnection(tb);
                // handle menu status
                itemAll.setEnabled(true);
                itemExpand.setEnabled(true);
            }
        });
        // collapse all other paths
        itemIsolated = new MenuItem(classMenu, SWT.PUSH);
        itemIsolated.setText("Isolate Path");
        itemIsolated.addSelectionListener(new SelectionListener() {

            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {

                try {

                    // clear the View
                    clearView();

                    branchFilter = new BranchFilter(
                            new ETPath(getRootETNode(getSelectedNode()),
                                    getSelectedNode()));

                    TreeBranch tb = buildTreeBranch(
                            getRootETNode(getSelectedNode()), null,
                            branchFilter);

                    // add the isolated path
                    root.addBranch(tb);
                    activeFilter = branchFilter;
                    sketchStartUpConnection(tb);
                    // handle menu status
                    itemAll.setEnabled(true);
                    itemIsolated.setEnabled(false);

                } catch (RuntimeException e) {
                    MessageDialog.openInformation(PlatformUI.getWorkbench()
                            .getActiveWorkbenchWindow().getShell(),
                            "Collapse Tree",
                            "Failed to collapse tree! Please select a node.");
                    e.printStackTrace();
                }

            }

        });
        // show all other paths
        itemAll = new MenuItem(classMenu, SWT.PUSH);
        itemAll.setText("Show all");
        itemAll.setEnabled(false);
        itemAll.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {

                // set new root
                setCurrentETRootNode(getRootETNode(getSelectedNode()));

                // clean up
                branchFilter = null;
                collapseFilter.clearCollapseMarkers(currentETRootNode);
                collapseFilter.clear();

                itemIsolated.setEnabled(true);
                refresh();

            }

        });
        item = new MenuItem(classMenu, SWT.SEPARATOR);
        // create test case button
        item = new MenuItem(classMenu, SWT.PUSH);
        item.setText("Create Test Cases For Path");
        item.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {

                if (ExecutionTreeView.this.selected instanceof LeafNode) {
                    ETLeafNode leaf = ((LeafNode) ExecutionTreeView.this.selected)
                            .getETLeafNode();
                    VBTBuilder builder = new VBTBuilder(leaf
                            .getProofTreeNodes(), ModelGenerator.SIMPLIFY);

                    if (!builder.succesful())
                        MessageDialog.openError(PlatformUI.getWorkbench()
                                .getActiveWorkbenchWindow().getShell(),
                                "Test Case Generation",
                                "An error occured during test case generation");

                    else if (builder.newProjectCreated())

                        MessageDialog
                                .openInformation(
                                        PlatformUI.getWorkbench()
                                                .getActiveWorkbenchWindow()
                                                .getShell(),
                                        "Test Case Generation",
                                        "A test case for the selected execution path was generated.\n"
                                                + "It was written to "
                                                + builder.getFileName()
                                                + "\n"
                                                + "in the default package of the new created project "
                                                + builder.getTestGenProject()
                                                        .getName());
                    else
                        MessageDialog
                                .openInformation(
                                        PlatformUI.getWorkbench()
                                                .getActiveWorkbenchWindow()
                                                .getShell(),
                                        "Test Case Generation",
                                        "A test case for the selected execution path was generated.\n"
                                                + "It was written to "
                                                + builder.getFileName()
                                                + " \nin the default packege of project "
                                                + builder.getTestGenProject()
                                                        .getName());
                }

            }
        });

    }

    /**
     * Double click.
     * 
     * @param node
     *            the node
     */
    void doubleClick(SourceElementFigure node) {
        ICompilationUnit cu = node.getUnit();
        try {
            IEditorPart ed = JavaUI.openInEditor(cu);
            ISourceViewer viewer = (ISourceViewer) ed
                    .getAdapter(ITextOperationTarget.class);

            int s = node.getASTNode().getStartPosition();
            int o = node.getASTNode().getLength();
            viewer.setSelectedRange(s, o);
            viewer.revealRange(s, o);
        } catch (PartInitException e) {
            e.printStackTrace();
        } catch (JavaModelException e) {
            e.printStackTrace();
        }

        this.maxmerge++;
        this.merged = 0;
    }

    /**
     * Fill local tool bar.
     * 
     * @param manager
     *            the manager
     */
    private void fillLocalToolBar(IToolBarManager manager) {
        // manager.add(sletAction);
        // manager.add(msletAction);
        // //manager.
        // manager.add(this.useBranchLabelsAction);
        manager.add(clearViewAction);
        manager.add(new Separator());
        manager.add(clearWatchpoints);
        manager.add(new Separator());
        manager.add(recomputeWatchpoints);
        manager.add(new Separator());
        manager.add(decisionProcedureAction);
        manager.add(new Separator());
        manager.add(this.testCaseAction);
        // manager.add(stepIntoAction);
        // manager.add(stepOverAction);
    }

    /**
     * Find branch.
     * 
     * @param b
     *            the b
     * @param etn
     *            the etn
     * 
     * @return the tree branch
     */
    private TreeBranch findBranch(TreeBranch b, ETMethodInvocationNode etn) {

        while (b != null) {

            if (b.getNode() instanceof MethodInvocationFigure) {
                MethodInvocationFigure mif = (MethodInvocationFigure) b
                        .getNode();
                if (mif.getETNode() == etn) {
                    return b;
                }
            }
            b = b.getParentTB();
        }
        return null;

    }

    // TODO move to VisualDebugger
    /**
     * Gets the subtree goals for et node.
     * 
     * @param etNode
     *            the et node
     * 
     * @return the subtree goals for et node
     */
    private ImmutableList<Goal> getSubtreeGoalsForETNode(ETNode etNode) {
        final ITNode[] itNodes = etNode.getITNodesArray();
        ImmutableList<Goal> goals = ImmutableSLList.<Goal>nil();
        for (int i = 0; i < itNodes.length; i++) {
            final ImmutableList<Goal> g = vd.getMediator().getProof().getSubtreeGoals(
                    (itNodes[i].getNode()));
            goals = goals.prepend(g);
        }
        return goals;

    }

    /**
     * Hook shell.
     */
    private void hookShell() {
        Composite localShell = new Composite(parent, 0);
        // localShell.set
        GridData gdata = new GridData(GridData.FILL_VERTICAL);
        // gdata.minimumWidth=30;
        // gdata.grabExcessHorizontalSpace=true;
        localShell.setLayoutData(gdata);

        localShell.setLayout(new GridLayout());

        Group progressGroup = new Group(localShell, 0);
        RowLayout progressGroupLayout = new RowLayout(
                org.eclipse.swt.SWT.HORIZONTAL);
        progressGroup.setLayout(progressGroupLayout);
        GridData progressGroupLData = new GridData();
        progressGroupLData.widthHint = 237;
        progressGroupLData.heightHint = 23;
        progressGroup.setLayoutData(progressGroupLData);
        progressGroup.setText("Progress");

        RowData progressBar1LData = new RowData();
        progressBar1LData.width = 230;
        progressBar1LData.height = 12;
        progressBar1 = new ProgressBar(progressGroup, SWT.NONE);
        progressBar1.setLayoutData(progressBar1LData);
        progressBar1.setMinimum(-1);

        // Instaniate a new ProgressMonitor to provide feedback over long
        // running task
        PM pm = new PM(progressBar1);
        // Register Progressmonitor to the VisualDebugger

        vd.addPMtoProofStarter(pm);

        Group rootGroup = new Group(localShell, 0);
        rootGroup.setText("Properties");
        FontData data = rootGroup.getFont().getFontData()[0];
        data.setStyle(SWT.BOLD);
        rootGroup.setLayout(new GridLayout());
        GridData rootGroupLData = new GridData();
        rootGroupLData.widthHint = 237;
        rootGroupLData.heightHint = 134;
        rootGroup.setLayoutData(rootGroupLData);
        // for development purpose...disabled in normal runs
        if (debug) {
            final Button orientation = new Button(rootGroup, SWT.RADIO);
            orientation.setText("Raw Tree");
            orientation
                    .setSelection(ExecutionTree.treeStyle == ExecutionTree.RAWTREE);
            orientation.addSelectionListener(new SelectionAdapter() {
                public void widgetSelected(SelectionEvent e) {
                    ExecutionTree.treeStyle = ExecutionTree.RAWTREE;
                    refresh();
                }
            });

            final Button orientation2 = new Button(rootGroup, SWT.RADIO);
            orientation2.setText("Statement Level Execution Tree");
            orientation2
                    .setSelection(ExecutionTree.treeStyle == ExecutionTree.SLET);
            orientation2.addSelectionListener(new SelectionAdapter() {
                public void widgetSelected(SelectionEvent e) {
                    ExecutionTree.treeStyle = ExecutionTree.SLET;
                    refresh();
                }
            });

            final Button orientation3 = new Button(rootGroup, SWT.RADIO);
            orientation3.setText("Statement Level Execution Tree2");
            orientation3
                    .setSelection(ExecutionTree.treeStyle == ExecutionTree.SLET2);
            orientation3.addSelectionListener(new SelectionAdapter() {
                public void widgetSelected(SelectionEvent e) {
                    ExecutionTree.treeStyle = ExecutionTree.SLET2;
                    refresh();
                }
            });

            final Button orientation6 = new Button(rootGroup, SWT.RADIO);
            orientation6.setText("Statement Level Execution Tree3");
            orientation6
                    .setSelection(ExecutionTree.treeStyle == ExecutionTree.SLET3);
            orientation6.addSelectionListener(new SelectionAdapter() {
                public void widgetSelected(SelectionEvent e) {
                    ExecutionTree.treeStyle = ExecutionTree.SLET3;
                    refresh();
                }
            });

        }

        if (debug) {
            Group rootGroup2 = new Group(localShell, 0);
            rootGroup.setText("Properties");
            FontData data2 = rootGroup2.getFont().getFontData()[0];
            data2.setStyle(SWT.BOLD);
            rootGroup2.setLayout(new GridLayout());

            final Button hideInfButton = new Button(rootGroup2, SWT.CHECK);
            hideInfButton.setText("Hide Infeasible Paths");
            hideInfButton.setSelection(hideInfeasible);

            hideInfButton.addSelectionListener(new SelectionAdapter() {
                public void widgetSelected(SelectionEvent e) {
                    hideInfeasible = hideInfButton.getSelection();
                    refresh();
                }
            });
        }

        final org.eclipse.swt.widgets.Label majorLabel = new org.eclipse.swt.widgets.Label(
                rootGroup, 0);
        GridData majorLabelLData = new GridData();
        majorLabelLData.widthHint = 114;
        majorLabelLData.heightHint = 21;
        majorLabel.setLayoutData(majorLabelLData);
        majorLabel.setText("Major Spacing: 10");
        final Scale major = new Scale(rootGroup, 0);
        major.setLayoutData(new GridLayout());
        GridData majorLData = new GridData();
        majorLData.widthHint = 200;
        majorLData.heightHint = 32;
        major.setLayoutData(majorLData);

        major.setMinimum(10);
        major.setIncrement(10);
        major.setMaximum(200);
        major.setSelection(50);
        major.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
                root.setMajorSpacing(major.getSelection());
                majorLabel.setText("Major Spacing: " + root.getMajorSpacing());
            }
        });

        final org.eclipse.swt.widgets.Label minorLabel = new org.eclipse.swt.widgets.Label(
                rootGroup, 0);
        minorLabel.setText("Minor Spacing: 10");
        final Scale minor = new Scale(rootGroup, 0);
        minor.setLayoutData(new GridLayout());
        GridData minorLData = new GridData();
        minorLData.widthHint = 200;
        minorLData.heightHint = 32;
        minor.setLayoutData(minorLData);

        minor.setMinimum(10);
        minor.setIncrement(5);
        minor.setMaximum(100);
        minor.setSelection(30);
        minor.setSize(200, 25);
        minor.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
                root.setMinorSpacing(minor.getSelection());
                minorLabel.setText("Minor Spacing: " + root.getMinorSpacing());
            }
        });

        Group bcGroup = new Group(localShell, 0);
        bcGroup.setText("Branch Condition");

        GridData bcGroupLData = new GridData();
        bcGroupLData.verticalAlignment = GridData.FILL;
        bcGroupLData.horizontalAlignment = GridData.FILL;
        bcGroupLData.grabExcessHorizontalSpace = true;
        bcGroupLData.grabExcessVerticalSpace = true;
        bcGroup.setLayoutData(bcGroupLData);
        bcGroup.setLayout(new GridLayout());

        // list to display the branch conditions
        bcListControl = new List(bcGroup, SWT.READ_ONLY | SWT.MULTI
                | SWT.BORDER | SWT.WRAP | SWT.V_SCROLL | SWT.H_SCROLL);
        GridData bcListControlLData = new GridData();
        bcListControlLData.verticalAlignment = GridData.FILL;
        bcListControlLData.horizontalAlignment = GridData.FILL;
        bcListControlLData.grabExcessHorizontalSpace = true;
        bcListControlLData.grabExcessVerticalSpace = true;
        bcListControl.setLayoutData(bcListControlLData);

        // handle clicks in the list
        bcListControl.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {

                bcText.setText(bcListControl.getSelection()[0]);
                refresh();
            }
        });

        Group wpGroup = new Group(localShell, 0);
        wpGroup.setText("Watchpoint Information");

        GridData wpGroupLData = new GridData();
        wpGroupLData.verticalAlignment = GridData.FILL;
        wpGroupLData.horizontalAlignment = GridData.FILL;
        wpGroupLData.grabExcessHorizontalSpace = true;
        wpGroupLData.grabExcessVerticalSpace = true;
        wpGroup.setLayoutData(bcGroupLData);
        wpGroup.setLayout(new GridLayout());

        wpInfo = new List(wpGroup, SWT.READ_ONLY | SWT.MULTI | SWT.BORDER
                | SWT.WRAP | SWT.V_SCROLL | SWT.H_SCROLL);
        GridData wpInfoControlLData = new GridData();
        wpInfoControlLData.verticalAlignment = GridData.FILL;
        wpInfoControlLData.horizontalAlignment = GridData.FILL;
        wpInfoControlLData.grabExcessHorizontalSpace = true;
        wpInfoControlLData.grabExcessVerticalSpace = true;
        wpInfo.setLayoutData(wpInfoControlLData);
    }

    /**
     * Make actions.
     * 
     * Initializes and registers all actions
     */
    private void makeActions() {
        sletAction = new Action("SLET", IAction.AS_RADIO_BUTTON) {
            public void run() {
                // showMessage("Action 1 executed");
            }
        };

        sletAction.setToolTipText("Statement Level Execuion Tree");

        useBranchLabelsAction = new Action("BC Labels", IAction.AS_CHECK_BOX) {
            public void run() {
                bcLabels = useBranchLabelsAction.isChecked();
                if (currentRoot != null) {
                    // setLabelsVisible(bcLabels);
                    if (cutTree)
                        cutTree = false;
                    else
                        cutTree = true;

                }
            }
        };

        useBranchLabelsAction
                .setToolTipText("Label the branches of the tree with branch conditions");

        msletAction = new Action("MSLET", IAction.AS_RADIO_BUTTON) {
            public void run() {
                // showMessage("Action 1 executed");
            }
        };

        msletAction.setToolTipText("Minimal Statement Level Execuion Tree");

        testCaseAction = new Action() {
            public void run() {
                if (vd.getMediator().getProof() == null)
                    return;
                ImmutableList<Node> nodes = toList(vd.getMediator().getProof().root()
                        .leavesIterator());
                VBTBuilder builder = new VBTBuilder(nodes,
                        ModelGenerator.OLD_SIMPLIFY);

                if (!builder.succesful())
                    MessageDialog.openError(PlatformUI.getWorkbench()
                            .getActiveWorkbenchWindow().getShell(),
                            "Test Case Generation",
                            "An error occured during test case generation");

                else if (builder.newProjectCreated())

                    MessageDialog
                            .openInformation(
                                    PlatformUI.getWorkbench()
                                            .getActiveWorkbenchWindow()
                                            .getShell(),
                                    "Test Case Generation",
                                    "Test cases for the current execution tree were generated.\n"
                                            +

                                            "They were written to  "
                                            + builder.getFileName()
                                            + "\n"
                                            + "in the default package of the new created project "
                                            + builder.getTestGenProject()
                                                    .getName());
                else
                    MessageDialog.openInformation(PlatformUI.getWorkbench()
                            .getActiveWorkbenchWindow().getShell(),
                            "Test Case Generation",
                            "Test cases for the current execution tree were generated.\n"
                                    + "They were written to "
                                    + builder.getFileName()
                                    + "\nin the default package of project "
                                    + builder.getTestGenProject().getName());
            }

        };
        testCaseAction
                .setToolTipText("Create Test Cases for the Execution Tree");
        testCaseAction.setText("Create Test Cases");

        decisionProcedureAction = new Action() {
            public void run() {
                if (vd.getMediator().getProof() == null)
                    return;
                if (!vd.getMediator().ensureProofLoaded())
                    return;
                
                SMTRule r = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getActiveSMTRule();
                final Proof proof = vd.getMediator().getProof();
                RuleLauncher.INSTANCE.start(ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getActiveSMTRule(),
                	proof, proof.getUserConstraint().getConstraint(), true);
            }

        };
        decisionProcedureAction
                .setToolTipText("Runs an external decision procedure \nin order to find infeasible execution paths");
        decisionProcedureAction.setText("Run Decision Procedure");

        clearViewAction = new Action() {
            public void run() {
                clearView();
            }

        };
        clearViewAction.setToolTipText("clears the view");
        clearViewAction.setText("Clear View");
        
        clearWatchpoints = new Action() {
            public void run() {
                clearWatchpoints();
            }

        };
        clearWatchpoints.setToolTipText("removes all watchpoint markers (yellow borders)");
        clearWatchpoints.setText("Clear Watchpoints");

        recomputeWatchpoints = new Action() {
            public void run() {
                try {
                    LinkedList<ETNode> nodesToEvaluate;
                    Filter f = new TreeFilter();
                    currentETRootNode = getCurrentETRootNode();
                    if (activeFilter instanceof BranchFilter) {
                        f = branchFilter;
                        nodesToEvaluate = branchFilter.getPath().getPath();
                    } else {
                        if (activeFilter instanceof CollapseFilter) {
                            f = collapseFilter;
                            nodesToEvaluate = getETasList(currentETRootNode);
                            for (ETNode node : nodesToEvaluate) {
                                if (!f.filter(node)) {
                                    nodesToEvaluate.remove(node);
                                }
                            }
                        } else {
                            nodesToEvaluate = getETasList(currentETRootNode);
                        }
                    }
                    identifyWatchpoints(nodesToEvaluate);
                    // clear the View
                    clearView();
                    TreeBranch tb = buildTreeBranch(currentETRootNode, null, f);
                    // draw the new view of the tree
                    root.addBranch(tb);
                    sketchStartUpConnection(tb);
                } catch (OutOfMemoryError oome) {
                    System.out.println("OUT OF MEMORY ERROR!!!");
                } catch (Throwable t) {
                    System.out.println("An Error occured! \n\n" + t.toString());
                    t.printStackTrace();
                }
            }

        };
        recomputeWatchpoints
                .setToolTipText("recomputes all watchpoints for the current execution tree");
        recomputeWatchpoints.setText("Recompute Watchpoints");
    }

    /**
     * Gets the executiontree, respectively subtree according to the given
     * ETNode as list.
     * 
     * @param etn
     *            the ETNode containing the current ET
     * 
     * @return the executiontree as list
     */
    private LinkedList<ETNode> getETasList(ETNode etn) {

        LinkedList<ETNode> executionTree = new LinkedList<ETNode>();
        executionTree.add(etn);
        LinkedList<ETNode> children = etn.getChildrenList();
        for (ETNode node : children) {
            executionTree.addAll(getETasList(node));
        }
        System.out.println("This ET has " + executionTree.size() + " nodes.");
        return executionTree;
    }

    /**
     * Refresh.
     * 
     * Draws a new Execution Tree after 5 Steps
     */
    public synchronized void refresh() {

        try {
            if (currentRoot == null) {
                return;
            }
            clearView();
            /**
             * This distinction is only for debugging purposes and should be
             * removed in the final release. SLET3 is what the user normally
             * sees.
             * 
             */
            labels = new HashSet();
            TreeBranch treebranch = null;
            ETNode etn = ExecutionTree.getETNode();
            if (etn == null) {
                return;
            }

            if (ExecutionTree.treeStyle == ExecutionTree.SLET2) {

                treebranch = buildTreeBranch(ExecutionTree
                        .getEtTreeBeforeMerge(), null, new TreeFilter());
                this.root.addBranch(treebranch);
            } else

            if (ExecutionTree.treeStyle == ExecutionTree.SLET3) {
            	activeFilter = new TreeFilter();
                
//            	LinkedList<ETNode> allLeafETNodes = WatchpointUtil.getAllLeafETNodes(etn);
//				identifyWatchpoints(allLeafETNodes);
                
				treebranch = buildTreeBranch(etn, null, activeFilter);
                this.root.addBranch(treebranch);

            } else if (ExecutionTree.treeStyle == ExecutionTree.RAWTREE) {
                treebranch = buildRawTree(currentRoot);
                root.addBranch(treebranch);
            }

            if (treebranch != null)
                root.addLabel(createConnection(root.getNode(), treebranch
                        .getNode(), "", false));
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }

    /**
     * Removes the selection.
     */
    private void removeSelection() {
        // remove exception marker
        if (this.unitOfLastExceptionMarker != null) {
            try {
                this.unitOfLastExceptionMarker.getResource().deleteMarkers(
                        "VisualDebugger.exceptionmarker", false, 1);
            } catch (CoreException e1) {
                e1.printStackTrace();
            }
            this.unitOfLastExceptionMarker = null;

        }

        // remove selection of node
        if (selected != null) {
            if (selected instanceof LeafNode) {
                ((LeafNode) selected).setSelected(false);
            } else if (selected instanceof SourceElementFigure) {
                ((SourceElementFigure) selected).setSelected(false);
            } else if (selected instanceof MethodInvocationFigure) {
                ((MethodInvocationFigure) selected).setSelected(false);
            } else if (selected instanceof MethodReturnFigure) {
                ((MethodReturnFigure) selected).setSelected(false);
            }
        }

        if (this.selectedMIN != null) {
            selectedMIN.setSelected(false);
        }

    }

    /**
     * Repaint connections.
     */
    private void repaintConnections() {

        IFigure contents = root.getContentsPane();
        labels = new HashSet();

        if (!contents.getChildren().isEmpty()) {
            this.root.removeLabels();
        }

    }

    /**
     * Sets the branch condition text.
     * 
     * @param etn
     *            the new branch condition text
     */
    private void setBranchConditionText(ETNode etn) {
	if (etn != null) {
	    final ImmutableList<Term> simplifiedBc = etn.getSimplifiedBc();

	    if  (simplifiedBc != null && etn.getParent() != null
		    && etn.getParent().getChildrenList().size() > 1) {
		final String[] termsString = new String[simplifiedBc.size()];
		int i = 0;
		for (Term bc : simplifiedBc) {
		    termsString[i++] = vd.prettyPrint(bc);
		}
		bcListControl.setItems(termsString);
	    }
	} else
            bcListControl.setItems(new String[0]);

    }

    /**
     * Passing the focus request to the viewer's control.
     */
    public void setFocus() {

    }

    /**
     * Sets the leaf node selected.
     * 
     * @param node
     *            the new leaf node selected
     */
    private void setLeafNodeSelected(LeafNode node) {
        this.removeSelection();

        selected = node;
        node.setSelected(true);
        final ETLeafNode ln = node.getETLeafNode();
        this.setBranchConditionText(ln);

        if (ln.getExpression() != null) {
            SourceElementId id = ln.getExpression();
            Expression expr = Activator.getDefault()
                    .getExpression(id);
            ICompilationUnit unit = Activator.getDefault()
                    .getCompilationUnit(id);
            try {
                IEditorPart ed = JavaUI.openInEditor(unit);
                ISourceViewer viewer = (ISourceViewer) ed
                        .getAdapter(ITextOperationTarget.class);
                int s = expr.getStartPosition();
                int o = expr.getLength();
                viewer.setSelectedRange(s, o);
                viewer.revealRange(s, o);
            } catch (PartInitException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (JavaModelException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            // ____

            try {
                Map map = new HashMap();
                int s = expr.getStartPosition();
                int o = expr.getLength();

                // map.put("StatementId", visitor.getStatementId());
                // MarkerUtilities.setLineNumber(map, 10);
                MarkerUtilities.setCharStart(map, s);
                MarkerUtilities.setCharEnd(map, s + o);
                MarkerUtilities.setMessage(map, "Possible Uncaught Exception: "
                        + ln.getExceptionName());

                MarkerUtilities.createMarker(unit.getResource(), map,
                        "VisualDebugger.exceptionmarker");
                unitOfLastExceptionMarker = unit;

            } catch (CoreException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

        }

        vd.fireDebuggerEvent(new DebuggerEvent(DebuggerEvent.NODE_SELECTED,
                node.getETLeafNode()));

    }

    /**
     * Sets the selected.
     * 
     * @param node
     *            the new selected
     */
    void setSelected(MethodReturnFigure node) {
        this.removeSelection();
        selected = node;
        node.setSelected(true);

        ETMethodReturnNode etn = (node).getETNode();

        this.setBranchConditionText(etn);
        TreeBranch min = this.findBranch((TreeBranch) node.getParent(), etn
                .getParent().getLastMethodInvocation());
        this.selectedMIN = ((MethodInvocationFigure) min.getNode());
        ((MethodInvocationFigure) min.getNode()).setSelected(true);
        vd.fireDebuggerEvent(new DebuggerEvent(DebuggerEvent.NODE_SELECTED,
                node.getETNode()));
    }

    /**
     * Sets the selected.
     * 
     * @param node
     *            the new selected
     */
    void setSelected(SourceElementFigure node) {
        this.removeSelection();
        selected = node;
        node.setSelected(true);

        ETNode etn = (node).getETNode();
        this.setBranchConditionText(etn);
        vd.fireDebuggerEvent(new DebuggerEvent(DebuggerEvent.NODE_SELECTED,
                node.getETNode()));
    }

    /**
     * Start refresh thread.
     */
    public void startRefreshThread() {
        Display display = shell.getDisplay();
        final Thread barThread = new Thread("PBarThread") {
            public void run() {
                ExecutionTreeView.this.refresh();
            }
        };
        display.asyncExec(barThread);
    }

    /**
     * To list.
     * 
     * @param it
     *            the it
     * 
     * @return the list of node
     */
    private ImmutableList<Node> toList(Iterator<Node> it) {
        ImmutableList<Node> result = ImmutableSLList.<Node>nil();
        while (it.hasNext()) {
            result = result.append(it.next());

        }
        return result;

    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.visualdebugger.DebuggerListener#update(de.uka.ilkd.key.visualdebugger.DebuggerEvent)
     */
    public synchronized void update(DebuggerEvent event) {
        if (event.getType() == DebuggerEvent.TREE_CHANGED) {
            this.currentRoot = (ITNode) event.getSubject();
            startRefreshThread();
            
        } else if (event.getType() == DebuggerEvent.TEST_RUN_FAILED) {
            final VisualDebugger.TestCaseIdentifier tci = (VisualDebugger.TestCaseIdentifier) event
                    .getSubject();
            Display display = shell.getDisplay();
            final Thread barThread = new Thread("Failed Test C Thread") {
                public void run() {
                    VisualDebugger.print("Execution Tree view: failed tc: "
                            + tci);
                    Node n = vd.getNodeForTC(tci.getFile(), tci.getMethod());
                    VisualDebugger.print("Node found: " + n.serialNr());
                    if (n != null) {
                        TreeBranch tb = root.findNode(n);
                        if (tb != null) {

                            tb.markBranch();
                        }

                    }

                    MessageDialog
                            .openInformation(
                                    PlatformUI.getWorkbench()
                                            .getActiveWorkbenchWindow()
                                            .getShell(),
                                    "Test Case Generation",
                                    "Test run of method "
                                            + tci.getMethod()
                                            + " in file "
                                            + tci.getFile()
                                            + " failed.\n"
                                            + "The corresponding execution path in the execution tree is highlighted.");

                }
            };
            display.asyncExec(barThread);

        } else if (event.getType() == DebuggerEvent.PROJECT_LOADED_SUCCESSFUL) {
            this.setBranchConditionText(null);
            // this.root.removeAll();

        }

    }

    /**
     * Clear the view.
     */
    private void clearView() {

        IFigure contents = root.getContentsPane();
        // remove all existing children
        if (!contents.getChildren().isEmpty()) {
            ((Figure) contents).removeAll();
            root.removeLabels();
        }
    }
    /**
     * Removes the watchpoint markers(yellow borders) from the view.
     */ 
    private void clearWatchpoints() {
       LinkedList<ETNode> executionTree = WatchpointUtil.getETasList(getCurrentETRootNode());
       for (ETNode node : executionTree) {
        node.setWatchpoint(false);
    }
        refresh();
    }

    /**
     * Gets the progress bar1.
     * 
     * @return the progress bar1
     */
    public ProgressBar getProgressBar1() {
        return progressBar1;
    }

    /**
     * getSelectedNode
     * 
     * This method returns the node that is currently selected.
     * 
     * @return currentNode - the actual selected node
     */
    public ETNode getSelectedNode() {

        return ((DrawableNode) (ExecutionTreeView.this.selected)).getETNode();
    }

    /**
     * Sketch start up connection.
     * 
     * @param treeBranch
     *            the tree branch
     */
    private void sketchStartUpConnection(TreeBranch treeBranch) {
        // draw connection to start node
        if (treeBranch != null)
            root.addLabel(createConnection(root.getNode(),
                    treeBranch.getNode(), "", false));
    }

    /**
     * This method returns the rootETNode. The parameter can be a arbitrary node
     * in the tree.
     * 
     * @param currentNode
     *            the current node
     * 
     * @return the root et node
     */
    private ETNode getRootETNode(ETNode currentNode) {

        while (currentNode.getParent().getParent() != null) {
            currentNode = currentNode.getParent();
        }
        return currentNode;
    }

    /**
     * The Nested Class PM.
     * 
     * Implements the ProgressMonitor Interface to provide feedback over the
     * creation of the ET in the ExecutionTreeView, since this task can take
     * some time.
     */
    static class PM implements ProgressMonitor {

        /** The Progressbar pb. */
        private ProgressBar pb = null;

        /**
         * Instantiates a new PM.
         * 
         * @param pb
         *            the pb
         */
        public PM(ProgressBar pb) {
            this.pb = pb;
        }

        /*
         * (non-Javadoc)
         * 
         * @see de.uka.ilkd.key.util.ProgressMonitor#setProgress(int)
         */
        public void setProgress(final int progress) {

            Display.getDefault().syncExec(new Runnable() {
                public void run() {
                    // System.out.println(progress + ":" + pb.getMaximum());
                    pb.setSelection(progress);
                }
            });
        }

        /*
         * (non-Javadoc)
         * 
         * @see de.uka.ilkd.key.util.ProgressMonitor#setMaximum(int)
         */
        public void setMaximum(final int maximum) {
            Display.getDefault().syncExec(new Runnable() {
                public void run() {
                    pb.setMaximum(maximum);
                }
            });

        }
    }

    /**
     * Sets the current ETRootNode.
     * 
     * @param currentETRootNode
     *            the new current root ETNode
     */
    private void setCurrentETRootNode(ETNode currentETRootNode) {

        this.currentETRootNode = currentETRootNode;
    }

    /**
     * Gets the current ETRootNode. This makes sure we can track all children.
     * 
     * @return the currentETRootNode
     */
    private ETNode getCurrentETRootNode() {

        if (currentETRootNode == null) {
            return getRootETNode(ExecutionTree.getETNode());
        }
        return currentETRootNode;
    }
}
