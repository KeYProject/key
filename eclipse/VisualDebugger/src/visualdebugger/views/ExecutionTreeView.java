package visualdebugger.views;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

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
import org.eclipse.swt.widgets.*;
import org.eclipse.swt.widgets.Button;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.MarkerUtilities;

import visualdebugger.VBTBuilder;
import visualdebugger.draw2d.*;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.decproc.DecProcRunner;
import de.uka.ilkd.key.unittest.ModelGenerator;
import de.uka.ilkd.key.visualdebugger.*;
import de.uka.ilkd.key.visualdebugger.executiontree.*;

public class ExecutionTreeView extends ViewPart implements DebuggerListener {
    private static final boolean debug = false;

    private boolean bcLabels = true;

    List bcListControl;

    Menu classMenu;

    ITNode currentRoot = null;

    private boolean cutTree = false;

    FigureCanvas figureCanvas;

    boolean hideInfeasible = true;

    HashSet labels = new HashSet();

    LightweightSystem lws;

    int maxmerge = 0;

    int merged = 0;

    private Action msletAction;

    Composite parent;

    TreeRoot root;

    private Figure selected;

    private MethodInvocationFigure selectedMIN = null;

    Shell shell;

    private Action sletAction;

    private Action testCaseAction, decisionProcedureAction;

    private ICompilationUnit unitOfLastExceptionMarker = null;

    private Action useBranchLabelsAction;

    final VisualDebugger vd;

    public ExecutionTreeView() {
        vd = VisualDebugger.getVisualDebugger();
        vd.addListener(this);

    }

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

    public synchronized TreeBranch buildTreeBranch(ETNode n, TreeBranch parent) {
        try {
            IFigure statementNode = createNode(n);
            statementNode.addMouseListener(new MouseListener.Stub() {
                public void mousePressed(MouseEvent event) {
                    if (event.button == 3) {
                        classMenu.setVisible(true);
                    }
                }
            });

            createRighClickContextMenu();

            TreeBranch branch = new TreeBranch(statementNode, parent);
            ETNode[] children = n.getChildren();
            if (children != null && children.length > 0) {
                for (int i = 0; i < children.length; i++) {
                    TreeBranch subTree = buildTreeBranch(children[i], branch);
                    branch.addBranch(subTree, children[i].getBC() + "");
                    // subTree.getNode()

                    // subTree.

                    final Connection c = createConnection(statementNode,
                            subTree.getNode(), children[i].getBC() != null ? vd
                                    .prettyPrint(children[i].getSimplifiedBc())
                                    : "NO BC", (children.length > 1));
                    subTree.setConnection(c);

                    // c.setForegroundColor(ColorConstants.red);
                    root.addLabel(c);
                    // }
                }
            }
            return branch;
        } catch (Throwable t) {
            t.printStackTrace();
        }
        return null;
    }

    private void contributeToActionBars() {
        IActionBars bars = getViewSite().getActionBars();
        // fillLocalPullDown(bars.getMenuManager());
        fillLocalToolBar(bars.getToolBarManager());
    }

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

    private Figure createNode(ETNode etNode) {
        if (etNode instanceof ETStatementNode) {
            final SourceElementFigure node = new SourceElementFigure(
                    (ETStatementNode) etNode);

            node.addMouseListener(new MouseListener.Stub() {
                public void mouseDoubleClicked(MouseEvent me) {
                    doubleClick(node);
                }

                public void mousePressed(MouseEvent me) {
                    setSelected(node);
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

            // if (true)
            // return new Label("TEST");

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
     */
    public void createPartControl(Composite parent) {
        shell = parent.getShell();
        this.parent = parent;
        // parent.setLayout(new GridLayout(2, false));
        parent.setLayout(new GridLayout(2, false));
        figureCanvas = new FigureCanvas(parent, SWT.NONE);
        figureCanvas.setScrollBarVisibility(FigureCanvas.AUTOMATIC);

        figureCanvas.getViewport().setContentsTracksHeight(true);
        figureCanvas.getViewport().setContentsTracksWidth(true);
        figureCanvas.getViewport().setContentsTracksHeight(true);
        figureCanvas.getViewport().setContentsTracksWidth(true);
        figureCanvas.setLayoutData(new GridData(GridData.FILL_BOTH));

        hookShell();

        // Put the LWS on the newly created Canvas.
        // lws = new LightweightSystem(canvas);

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

        if (vd.getCurrentTree() != null) {
            this.currentRoot = vd.getCurrentTree();
            this.refresh();
        }
    }

    private void createRighClickContextMenu() {
        classMenu = new Menu(shell, SWT.POP_UP);

        MenuItem item = new MenuItem(classMenu, SWT.PUSH);
        item.setText("Run");
        item.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent event) {
            }

            public void widgetSelected(SelectionEvent event) {
                final ListOfGoal goals = getSubtreeGoalsForETNode(((SourceElementFigure) ExecutionTreeView.this.selected)
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
                final ListOfGoal goals = getSubtreeGoalsForETNode(node);
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
                final ListOfGoal goals = getSubtreeGoalsForETNode(((SourceElementFigure) ExecutionTreeView.this.selected)
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
                vd.visualize(((SourceElementFigure) ExecutionTreeView.this.selected)
                                .getETNode().getITNodesArray()[0]);

            }

        });

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

    private void fillLocalToolBar(IToolBarManager manager) {
        // manager.add(sletAction);
        // manager.add(msletAction);
        // //manager.
        // manager.add(this.useBranchLabelsAction);
        manager.add(decisionProcedureAction);
        manager.add(new Separator());
        manager.add(this.testCaseAction);
        // manager.add(stepIntoAction);
        // manager.add(stepOverAction);
    }

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
    private ListOfGoal getSubtreeGoalsForETNode(ETNode etNode) {
        final ITNode[] itNodes = etNode.getITNodesArray();
        ListOfGoal goals = SLListOfGoal.EMPTY_LIST;
        for (int i = 0; i < itNodes.length; i++) {
            final ListOfGoal g = vd.getMediator().getProof().getSubtreeGoals(
                    (itNodes[i].getNode()));
            goals = goals.prepend(g);
        }
        return goals;

    }

    private void hookShell() {
        Composite localShell = new Composite(parent, 0);
        // localShell.set
        GridData gdata = new GridData(GridData.FILL_VERTICAL);
        // gdata.minimumWidth=30;
        // gdata.grabExcessHorizontalSpace=true;
        localShell.setLayoutData(gdata);

        localShell.setLayout(new GridLayout());

        Group rootGroup = new Group(localShell, 0);
        rootGroup.setText("Properties");
        FontData data = rootGroup.getFont().getFontData()[0];
        data.setStyle(SWT.BOLD);
        rootGroup.setLayout(new GridLayout());
        rootGroup.setLayoutData(new GridData(200, SWT.DEFAULT));

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
        majorLabel.setText("Major Spacing: 10");
        final Scale major = new Scale(rootGroup, 0);
        major.setLayoutData(new GridLayout());
        major.setLayoutData(new GridData(100, SWT.DEFAULT));

        major.setSize(200, 200);
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
        minor.setLayoutData(new GridData(100, SWT.DEFAULT));

        minor.setMinimum(10);
        minor.setIncrement(5);
        minor.setMaximum(100);
        minor.setSelection(30);
        minor.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
                root.setMinorSpacing(minor.getSelection());
                minorLabel.setText("Minor Spacing: " + root.getMinorSpacing());
            }
        });

        // text = new Text(localShell,SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL
        // );
        // text.setEditable(false);
        // Color white = new Color(null,255,255,255);
        // text.setBackground(white);

        Group bcGroup = new Group(localShell, 0);
        bcGroup.setBackground(ColorConstants.white);
        bcGroup.setText("Branch Condition");
        bcGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
        bcGroup.setLayout(new GridLayout());

        bcListControl = new List(bcGroup, SWT.READ_ONLY | SWT.MULTI
                | SWT.BORDER | SWT.WRAP | SWT.V_SCROLL | SWT.H_SCROLL);
        // bcListControl.set
        bcListControl.setLayoutData(new GridData(GridData.FILL_BOTH));
        // l = new org.eclipse.swt.widgets.Label(bcGroup, SWT.WRAP |
        // SWT.V_SCROLL);
        // l.setLayoutData(new GridData(GridData.FILL_BOTH));
        // l.setBackground(ColorConstants.white);

        // text.setLayoutData(recvData);
        // l.setText("TEST TEST TEST TEST TEST TESTTEST TEST TESTTEST TEST
        // TESTTEST TEST TESTTEST TEST TESTTEST TEST TESTTEST TEST \n TESTTEST
        // TEST TEST");

        // l.set
        // text.s
        // text.setSize(new Point(100,100));
        // text.setBounds(2, y, width, height)
        // text.

    }

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
                .setToolTipText("Label the the branches of the tree with branch conditions");

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
                ListOfNode nodes = toList(vd.getMediator().getProof().root()
                        .leavesIterator());
                VBTBuilder builder = new VBTBuilder(nodes,
                        ModelGenerator.SIMPLIFY);

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
                new DecProcRunner(Main.getInstance(false)).run();
            }

        };
        decisionProcedureAction
                .setToolTipText("Runs an external decision procedure \nin order to find infeasible execution paths");
        decisionProcedureAction.setText("Run Decision Procedure");
    }

    public synchronized void refresh() {
        try {
            if (currentRoot == null) {
                return;
            }

            IFigure contents = root.getContentsPane();

            labels = new HashSet();
            TreeBranch s = null;
            if (!contents.getChildren().isEmpty()) {
                ((Figure) contents).removeAll();
                this.root.removeLabels();
            }

            if (ExecutionTree.getETNode() == null) {
                return;
            }

            if (ExecutionTree.treeStyle == ExecutionTree.SLET2) {
                this.root.addBranch(s = buildTreeBranch(ExecutionTree
                        .getEtTreeBeforeMerge(), null));
            } else

            if (ExecutionTree.treeStyle == ExecutionTree.SLET3) {
                this.root.addBranch(s = buildTreeBranch(ExecutionTree
                        .getETNode(), null));
            } else if (ExecutionTree.treeStyle == ExecutionTree.RAWTREE)
                root.addBranch(s = buildRawTree(currentRoot));
            if (s != null)
                root.addLabel(createConnection(root.getNode(), s.getNode(), "",
                        false));
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }

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

    private void repaintConnections() {

        IFigure contents = root.getContentsPane();
        labels = new HashSet();

        if (!contents.getChildren().isEmpty()) {
            this.root.removeLabels();
        }

    }

    private void setBranchConditionText(ETNode etn) {

        if (etn != null && etn.getSimplifiedBc() != null
                && etn.getParent() != null
                && etn.getParent().getChildrenList().size() > 1) {

            final Term[] bc = etn.getSimplifiedBc().toArray();
            final String[] termsString = new String[bc.length];

            // text.setItems();
            for (int i = 0; i < bc.length; i++) {
                termsString[i] = (vd.prettyPrint(bc[i]));
            }

            bcListControl.setItems(termsString);
        } else
            bcListControl.setItems(new String[0]);

    }

    /**
     * Passing the focus request to the viewer's control.
     */
    public void setFocus() {

    }

    private void setLeafNodeSelected(LeafNode node) {
        this.removeSelection();

        selected = node;
        node.setSelected(true);
        final ETLeafNode ln = node.getETLeafNode();
        this.setBranchConditionText(ln);

        if (ln.getExpression() != null) {
            SourceElementId id = ln.getExpression();
            Expression expr = visualdebugger.Activator.getDefault()
                    .getExpression(id);
            ICompilationUnit unit = visualdebugger.Activator.getDefault()
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

    void setSelected(SourceElementFigure node) {
        this.removeSelection();
        selected = node;
        node.setSelected(true);

        ETNode etn = (node).getETNode();
        this.setBranchConditionText(etn);
        vd.fireDebuggerEvent(new DebuggerEvent(DebuggerEvent.NODE_SELECTED,
                node.getETNode()));
    }

    public void startRefreshThread() {
        Display display = shell.getDisplay();
        final Thread barThread = new Thread("PBarThread") {
            public void run() {
                ExecutionTreeView.this.refresh();
            }
        };
        display.asyncExec(barThread);
    }

    private ListOfNode toList(IteratorOfNode it) {
        ListOfNode result = SLListOfNode.EMPTY_LIST;
        while (it.hasNext()) {
            result = result.append(it.next());

        }
        return result;

    }

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

}
