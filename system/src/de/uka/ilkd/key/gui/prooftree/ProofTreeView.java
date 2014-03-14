// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//


package de.uka.ilkd.key.gui.prooftree;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Font;
import java.awt.Toolkit;
import java.awt.event.*;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;

import javax.swing.Icon;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JComponent;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JScrollPane;
import javax.swing.JSeparator;
import javax.swing.JTree;
import javax.swing.KeyStroke;
import javax.swing.ToolTipManager;
import javax.swing.UIManager;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.plaf.TreeUI;
import javax.swing.plaf.basic.BasicTreeUI;
import javax.swing.plaf.metal.MetalTreeUI;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeCellRenderer;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.gui.RuleAppListener;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.macros.ProofMacroMenu;
import de.uka.ilkd.key.gui.nodeviews.TacletInfoToggle;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.util.Debug;

public class ProofTreeView extends JPanel {

    private static final long serialVersionUID = 3732875161168302809L;
    private static final Color GRAY_COLOR = Color.DARK_GRAY;
    private static final Color BISQUE_COLOR = new Color(240,228,196);
    private static final Color LIGHT_BLUE_COLOR = new Color(230,254,255);
    private static final Color DARK_BLUE_COLOR = new Color(31,77,153);
    private static final Color DARK_GREEN_COLOR = new Color(0,128,51);
    private static final Color DARK_RED_COLOR = new Color(191,0,0);
    private static final Color ORANGE_COLOR = new Color(255,140,0);

    /** the mediator is stored here */
    private KeYMediator mediator;

    /** The JTree that is used for actual display and interaction */
    final JTree delegateView;

    /** the model that is displayed by the delegateView */
    GUIProofTreeModel delegateModel;

    private HashMap<Proof, GUIProofTreeModel> models = new LinkedHashMap<Proof, GUIProofTreeModel>(20);

    /** the proof this view shows */
    private Proof proof;

    /** the expansion state of the proof tree */
    private ExpansionState expansionState;

    /** listener */
    private GUIProofTreeProofListener proofListener;
    private GUITreeSelectionListener treeSelectionListener;
    private GUIProofTreeGUIListener guiListener;

    /** KeYStroke for the search panel: STRG+SHIFT+F */
    public final static KeyStroke searchKeyStroke = KeyStroke.getKeyStroke(KeyEvent.VK_F,
            java.awt.event.InputEvent.CTRL_DOWN_MASK
            | java.awt.event.InputEvent.SHIFT_DOWN_MASK
            | Toolkit.getDefaultToolkit().getMenuShortcutKeyMask());

    private ConfigChangeListener configChangeListener =  new ConfigChangeListener() {
                                            public void configChanged(ConfigChangeEvent e) {
                                                setProofTreeFont();
                                            }
                                        };
    /**
     * Roots of subtrees containing all nodes to which rules have been
     * applied; this is used when auto mode is active
     */
    private ImmutableList<Node> modifiedSubtrees      = null;
    private HashSet<Node>    modifiedSubtreesCache = null;

    /** the search dialog */
    private ProofTreeSearchBar proofTreeSearchPanel;

    // Taclet info can be shown for inner nodes.
    public final TacletInfoToggle tacletInfoToggle = new TacletInfoToggle();


    /** creates a new proof tree */
    public ProofTreeView (KeYMediator mediator) {

	proofListener = new GUIProofTreeProofListener();
        guiListener = new GUIProofTreeGUIListener();
        delegateView = new JTree(
                new DefaultMutableTreeNode("No proof loaded")) {
            private static final long serialVersionUID = 6555955929759162324L;

            public void updateUI() {
                super.updateUI();
                /* we want plus/minus signs to expand/collapse tree nodes */
                final TreeUI ui = getUI();
                if (ui instanceof BasicTreeUI) {
                    final BasicTreeUI treeUI = (BasicTreeUI) ui;
                    treeUI.setExpandedIcon(IconFactory.expandedIcon());
                    treeUI.setCollapsedIcon(IconFactory.collapsedIcon());
                }
                if (ui instanceof CacheLessMetalTreeUI) {
                    ((CacheLessMetalTreeUI) ui).clearDrawingCache();
                }
            }
        };

        delegateView.setUI(new CacheLessMetalTreeUI());

        delegateView.getInputMap(JComponent.WHEN_FOCUSED).getParent().remove(KeyStroke.getKeyStroke(KeyEvent.VK_UP, InputEvent.CTRL_MASK));
        delegateView.getInputMap(JComponent.WHEN_FOCUSED).getParent().remove(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, InputEvent.CTRL_MASK));


	delegateView.setInvokesStopCellEditing(true);
	delegateView.getSelectionModel().setSelectionMode
	    (TreeSelectionModel.SINGLE_TREE_SELECTION);
	treeSelectionListener = new GUITreeSelectionListener();
	delegateView.addTreeSelectionListener(treeSelectionListener);
	delegateView.setScrollsOnExpand(true);
        ToolTipManager.sharedInstance().registerComponent(delegateView);

        MouseListener ml = new MouseAdapter() {
            public void mousePressed(MouseEvent e) {
                if (e.isPopupTrigger()) {
                    TreePath selPath = delegateView.getPathForLocation
                        (e.getX(), e.getY());
                    if (selPath!=null && (selPath.getLastPathComponent()
                            instanceof GUIProofTreeNode ||
                            selPath.getLastPathComponent() instanceof
                            GUIBranchNode)) {
                        JPopupMenu popup = new ProofTreePopupMenu(selPath);
                        popup.show(e.getComponent(),
                                    e.getX(), e.getY());
                    }
                }
            }

            public void mouseReleased(MouseEvent e) {
                mousePressed(e);
            }
        };

	delegateView.addMouseListener(ml);

	setMediator(mediator);

        Config.DEFAULT.addConfigChangeListener(configChangeListener);

	setProofTreeFont();
	delegateView.setLargeModel(true);

        updateUI();

        setLayout(new BorderLayout());

        JPanel bottomPanel = new JPanel();
        bottomPanel.setLayout(new BorderLayout());
        bottomPanel.add(tacletInfoToggle, BorderLayout.NORTH);
        proofTreeSearchPanel = new ProofTreeSearchBar(this);
        bottomPanel.add(proofTreeSearchPanel, BorderLayout.SOUTH);

        add(new JScrollPane(delegateView), BorderLayout.CENTER);
        add(bottomPanel, BorderLayout.SOUTH);

	layoutKeYComponent();

	Proof selProof = mediator.getSelectedProof();
	if (selProof != null) {
	    setProof(selProof);
	}


	final ActionListener keyboardAction = new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
	        showSearchPanel();
	    }
	};

	registerKeyboardAction(keyboardAction,
	        searchKeyStroke,
	                JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
    }

    protected void finalize() throws Throwable {
        super.finalize();
        Config.DEFAULT.removeConfigChangeListener(configChangeListener);
    }

    private void setProofTreeFont() {
	Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_TREE);
	if (myFont != null) {
	    delegateView.setFont(myFont);
	} else {
	    Debug.out("KEY-PROOF_TREE_FONT not available, " +
		      "use standard font.");
	}
    }

    /** layout the component */
    protected void layoutKeYComponent() {
	delegateView.setBackground(Color.white);
	ProofRenderer renderer= new ProofRenderer();
	delegateView.setCellRenderer(renderer);
	delegateView.putClientProperty("JTree.lineStyle", "Angled");
	delegateView.setVisible(true);
    }


    /** returns the mediator to communicate with the model
     * @return the mediator to communicate with the model
     */
    public KeYMediator mediator() {
	return mediator;
    }

    /** sets the mediator to communicate with the model */
    private void setMediator(KeYMediator m) {
	if ( mediator != null )
	    unregister ();
	mediator = m;
	register();
    }

    private void register() {
	mediator.addKeYSelectionListener(proofListener);
	mediator.addAutoModeListener(proofListener);
	mediator.addGUIListener(guiListener);
    }

    private void unregister() {
	mediator.removeKeYSelectionListener(proofListener);
	mediator.removeAutoModeListener(proofListener);
	mediator.removeGUIListener(guiListener);
    }

    public void removeNotify () {
	unregister ();
	try{
	    delegateModel.unregister ();
        } catch(NullPointerException e)
	    { Debug.out("Exception thrown by class ProofTreeView at unregister()");
        }
	super.removeNotify ();
    }

    /**
     * sets up the proof tree view if a proof has been loaded
     * @param p the Proof that has been loaded
     */
    private void setProof(Proof p) {
	if (delegateModel != null) {
            expansionState.disconnect(delegateView);
            delegateModel.storeExpansionState(
                expansionState.state(new LinkedHashSet()));
            delegateModel.storeSelection(delegateView.getSelectionPath());
	    delegateModel.unregister();
            delegateModel.removeTreeModelListener(proofTreeSearchPanel);
	}

	if (proof != null) {
	   proof.removeRuleAppListener(proofListener);
	}
	proof = p;
   if (proof != null) {
      proof.addRuleAppListener(proofListener);
   }

        if (proof !=null) {
	    delegateModel = models.get(p);
            if (delegateModel == null) {
               delegateModel = new GUIProofTreeModel(p);
               models.put(p, delegateModel);
            }
            delegateModel.addTreeModelListener(proofTreeSearchPanel);
            delegateModel.register();
	    delegateView.setModel(delegateModel);
            expansionState =
                new ExpansionState(delegateView,
                    delegateModel.getExpansionState());
            delegateView.expandRow(0);
            delegateView.setSelectionPath(delegateModel.getSelection());
            delegateView.scrollPathToVisible(delegateModel.getSelection());
        } else {
            delegateModel = null;
	    delegateView.setModel(new DefaultTreeModel(new DefaultMutableTreeNode("No proof loaded.")));
            expansionState = null;
        }
        proofTreeSearchPanel.reset();
    }


    public void removeProof(Proof p) {
        models.remove(p);
    }

    public void removeProofs(Proof[] ps) {
        for (final Proof p : ps) {
	    models.remove(p);
	}
    }


    /**
     *  moves the scope of the tree view to the given node so that it
     *	is visible
     */
    public void makeNodeVisible(Node n) {
        if (n == null) return;

        final GUIAbstractTreeNode node = delegateModel.getProofTreeNode(n);
        if (node==null) return;

        TreeNode[] obs=node.getPath();
 	TreePath tp = new TreePath(obs);
	treeSelectionListener.ignoreChange = true;
 	delegateView.getSelectionModel().setSelectionPath(tp);
	delegateView.scrollPathToVisible(tp);
 	delegateView.validate();
	treeSelectionListener.ignoreChange = false;
    }


    protected void makeNodeExpanded(Node n) {
	GUIAbstractTreeNode node = delegateModel.getProofTreeNode(n);
 	if (node==null) return;
 	TreeNode[] obs=node.getPath();
 	TreePath tp = new TreePath(obs);
 	delegateView.makeVisible(tp);
    }


    /**
     * Collapse all subtrees that are closed
     */
    protected void collapseClosedNodes () {
	collapseClosedNodesHelp ( new TreePath ( delegateModel.getRoot () ) );
    }

    private void collapseClosedNodesHelp ( TreePath path ) {
	if ( !delegateView.isExpanded ( path ) )
	    return;

        Object node = path.getLastPathComponent();

	if ( node instanceof GUIBranchNode &&
		((GUIBranchNode)node).getNode ().isClosed() ) {
	    delegateView.collapsePath ( path );
	    return;
	}

        for ( int count = delegateModel.getChildCount(node), i = 0;
	      i < count;
	      i++ ) {
            Object child = delegateModel.getChild(node, i);
            if ( !delegateModel.isLeaf ( child ) )
		collapseClosedNodesHelp ( path.pathByAddingChild(child) );
        }
    }


    /**
     * Collapse all branches which are not below <tt>path</tt>
     */
    protected void collapseOthers(TreePath path) {
	collapseOthersHelp(new TreePath(delegateModel.getRoot()), path);
    }

    private void collapseOthersHelp(TreePath start, TreePath stop) {
	if ( !delegateView.isExpanded ( start ) || start.equals(stop))
	    return;

        Object node = start.getLastPathComponent();

	if ( node instanceof GUIBranchNode &&
	     !start.isDescendant(stop)) {
	    delegateView.collapsePath ( start );
	    return;
	}

        for ( int count = delegateModel.getChildCount(node), i = 0;
	      i < count;
	      i++ ) {
            Object child = delegateModel.getChild(node, i);
            if ( !delegateModel.isLeaf ( child ) )
		collapseOthersHelp ( start.pathByAddingChild(child), stop );
        }
    }

    /**
     * Selects the given Branchnode in the ProofTreeView and displays the
     * first child in the main view.
     */
    void selectBranchNode(GUIBranchNode node) {
        if (node == null) {
            return;
        }
        proofListener.ignoreNodeSelectionChange = true;
        mediator.getSelectionModel().setSelectedNode(
            node.getNode());
        proofListener.ignoreNodeSelectionChange = false;
        TreePath tp = new TreePath(node.getPath());
        treeSelectionListener.ignoreChange = true;
        delegateView.getSelectionModel().setSelectionPath(tp);
        delegateView.scrollPathToVisible(tp);
        delegateView.validate();
        treeSelectionListener.ignoreChange = false;

        delegateModel.storeSelection(delegateView.getSelectionPath());

    }

    /**
     * In auto mode, add a node which has been modified in a way
     * leading to structural changes of the proof tree
     */
    private void addModifiedNode( Node p_node ) {
        if ( modifiedSubtrees == null ) return;

	try {
	    if ( !modifiedSubtrees.isEmpty() ) {
		Node n = p_node;
		while ( true ) {
		    if ( modifiedSubtreesCache.contains ( n ) )
			return;
		    if ( n.root () )
			break;
		    n = n.parent ();
		}
	    }

	    modifiedSubtrees = modifiedSubtrees.prepend ( p_node );
	} finally {
	    modifiedSubtreesCache.add ( p_node );
	}
    }

    public void showSearchPanel() {
        proofTreeSearchPanel.setVisible(true);
    }

    // INNER CLASSES

    // listens to gui events
    class GUIProofTreeGUIListener implements GUIListener,
                                             java.io.Serializable {
	/**
         *
         */
        private static final long serialVersionUID = -7767170815005302177L;
    /** invoked if a frame that wants modal access is opened */
	public void modalDialogOpened(GUIEvent e) {
	    delegateView.setEnabled(false);
	}

	/** invoked if a frame that wants modal access is closed */
	public void modalDialogClosed(GUIEvent e) {
	    delegateView.setEnabled(true);
	}
	public void shutDown(GUIEvent e) {

	}
    }

    class GUIProofTreeProofListener implements AutoModeListener,
                                               RuleAppListener,
	                                       KeYSelectionListener {

	/** node of the last known current goal */
	private Node lastGoalNode;

        // hack to select Nodes without changing the selection of delegateView
        public boolean ignoreNodeSelectionChange = false;

	/** makes selected node visible of lastGoalNode */
	public void makeSelectedNodeVisible(Node selectedNode) {
            if (selectedNode != null ) {
                if ( proof != selectedNode.proof() ) {
                    return;
                }
                lastGoalNode = selectedNode;
            }

	    makeNodeVisible(lastGoalNode);
	    delegateView.validate();
	}

	/** focused node has changed */
	public void selectedNodeChanged(KeYSelectionEvent e) {
	    if (!ignoreNodeSelectionChange) {
	        makeSelectedNodeVisible(mediator.getSelectedNode());
	    }
	}

	/** the selected proof has changed (e.g. a new proof has been
	 * loaded) */
	public void selectedProofChanged(KeYSelectionEvent e) {
	    Debug.out("ProofTreeView: initialize with new proof");
	    lastGoalNode = null;
	    setProof(e.getSource().getSelectedProof());
	    delegateView.validate();
	}

	/** invoked if automatic application of rules has started
	 */
	public void autoModeStarted(ProofEvent e) {
	    modifiedSubtrees      = ImmutableSLList.<Node>nil();
	    modifiedSubtreesCache = new LinkedHashSet<Node>();
	    if (delegateModel == null) {
                Debug.out("delegateModel is null");
                return;
	    }
	    if (delegateModel.isAttentive()) {
		mediator.removeKeYSelectionListener(proofListener);
	    }
	    delegateModel.setAttentive(false);
	}

	/** invoked if automatic application of rules has stopped
	 */
	public void autoModeStopped(ProofEvent e) {
            if (mediator.getSelectedProof() == null) return; // no proof (yet)
            delegateView.removeTreeSelectionListener(treeSelectionListener);
	    if (delegateModel == null) {
		setProof(mediator.getSelectedProof());
	    } else if (modifiedSubtrees != null) {
		for (final Node n : modifiedSubtrees) {
		    delegateModel.updateTree (n);
		}
	    }
	    if (!delegateModel.isAttentive()) {
		delegateModel.setAttentive(true);
		mediator.addKeYSelectionListener(proofListener);
	    }
 	    makeSelectedNodeVisible(mediator.getSelectedNode());
	    delegateView.addTreeSelectionListener(treeSelectionListener);
 	    delegateView.validate();
	    modifiedSubtrees      = null;
	    modifiedSubtreesCache = null;
	}


       	/** invoked when a rule has been applied */
	public void ruleApplied(ProofEvent e) {
      addModifiedNode(e.getRuleAppInfo().getOriginalNode());
	}


    }

    class GUITreeSelectionListener implements TreeSelectionListener,
                                              java.io.Serializable {
	/**
         *
         */
        private static final long serialVersionUID = 1417544836006726419L;
    // hack to reduce duplicated repaints
	public boolean ignoreChange = false;

	public void valueChanged(TreeSelectionEvent e) {
	    if ( ignoreChange )
		return;
	    if (e.getNewLeadSelectionPath()==null) {
		return;
	    }
	    // catching ClassCastException occurring when clicking on
	    // "No proof loaded"
	    if (!(e.getNewLeadSelectionPath().
		 getLastPathComponent() instanceof GUIAbstractTreeNode)) {
		return;
	    }

	    TreePath newTP = e.getNewLeadSelectionPath();
	    delegateModel.storeSelection(newTP);


	    GUIAbstractTreeNode treeNode =
	            ((GUIAbstractTreeNode)e.getNewLeadSelectionPath().
	                    getLastPathComponent());
	    if (treeNode instanceof GUIBranchNode) {
	        selectBranchNode((GUIBranchNode)treeNode);
	    } else {
	        Node node = treeNode.getNode();
	        Goal selected = proof.getGoal(node);
	        if (selected != null) {
	            mediator.goalChosen(selected);
	        } else {
	            mediator.nonGoalNodeChosen(node);
	        }
	    }

	    // catching NullPointerException occurring when renaming root node
	    if (treeNode instanceof GUIBranchNode && treeNode
			.getNode().parent() != null) {
		delegateView.setEditable(true);
	    } else {
		delegateView.setEditable(false);
	    }
	}
    }

    class ProofRenderer extends DefaultTreeCellRenderer
	                implements TreeCellRenderer,
			           java.io.Serializable {

    /**
         *
         */
        private static final long serialVersionUID = -4990023575036168279L;
        private Icon keyHole20x20 = IconFactory.keyHole(20, 20);

	public Component getTreeCellRendererComponent(JTree tree,
						      Object value,
						      boolean sel,
						      boolean expanded,
						      boolean leaf,
						      int row,
						      boolean hasFocus) {
	    if (proof == null) {
	        // print dummy tree;
	        return super.getTreeCellRendererComponent(tree, value, sel,
	                expanded, leaf, row, hasFocus);
	    }

	    if (value instanceof GUIBranchNode) {
	        super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
                setBackgroundNonSelectionColor(BISQUE_COLOR);
                if ( ((GUIBranchNode)value).getNode().isClosed() ) {
                    // all goals below this node are closed
                    this.setIcon(IconFactory.provedFolderIcon());
                }
                return this;
            }

	    if (value instanceof GUIOneStepChildTreeNode) {
	        super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
                setForeground(GRAY_COLOR);
                setIcon(IconFactory.oneStepSimplifier(16));
                setText(value.toString());
                return this;
            }

            // now GUIProofTreeNode / GUIOneStepSimpTreeNode
	    Node node = ((GUIAbstractTreeNode)value).getNode();
	    String nodeText = node.serialNr()+":"+node.name();
	    boolean isBranch = false;
	    {
                final Node child = ((GUIAbstractTreeNode)value).findChild( node );
                if ( child != null && child.getNodeInfo()
                    .getBranchLabel () != null ) {
                    isBranch = true;
                    nodeText += ": " + child.getNodeInfo().getBranchLabel ();
                }
            }

	    DefaultTreeCellRenderer tree_cell =
		(DefaultTreeCellRenderer) super.getTreeCellRendererComponent
		(tree, nodeText, sel, expanded, leaf, row, hasFocus);



	    if (node.leaf()) {
		Goal goal = proof.getGoal(node);
		if ( goal == null || node.isClosed() ) {
		    tree_cell.setForeground(DARK_GREEN_COLOR);
		    tree_cell.setIcon(IconFactory.keyHoleClosed(20,20));
		    ProofTreeView.this.setToolTipText("Closed Goal");
		    tree_cell.setToolTipText("A closed goal");
		} else {
		    if ( !goal.isAutomatic() ) {
		        tree_cell.setForeground(ORANGE_COLOR);
		        tree_cell.setIcon(IconFactory.keyHoleInteractive(20, 20));
		        ProofTreeView.this.setToolTipText("Disabled Goal");
		        tree_cell.setToolTipText("Interactive goal - no automatic rule application");
		    } else {
			tree_cell.setForeground(DARK_RED_COLOR);
			tree_cell.setIcon(keyHole20x20);
			ProofTreeView.this.setToolTipText("Open Goal");
			tree_cell.setToolTipText("An open goal");
		    }
		}
	    } else {
		/*
		if ( node.getBranchSink ().getResetConstraint ().isSatisfiable () )
		    tree_cell.setForeground(Color.blue);
		else
		*/
		tree_cell.setForeground(Color.black);
                String tooltipText = "An inner node of the proof";
                final String notes = node.getNodeInfo().getNotes();
                if (notes!=null) {
                    tooltipText += ".\nNotes: "+notes;
                }

                Icon defaultIcon;
                if (notes != null) {
                    defaultIcon = IconFactory.editFile(16);
                } else if (node.getNodeInfo().getInteractiveRuleApplication()) {
                    defaultIcon = IconFactory.interactiveAppLogo(16);
                } else {
                    defaultIcon = null;
                }
                if (isBranch && node.childrenCount() > 1) {
                    defaultIcon = getOpenIcon();
                    tooltipText = "A branch node with all children hidden";
                }
                tree_cell.setIcon(defaultIcon);

		tree_cell.setToolTipText(tooltipText);
	    }

	    if (node.getNodeInfo().getNotes() != null) {
	        tree_cell.setBackgroundNonSelectionColor(ORANGE_COLOR);
	    } else
            if (node.getNodeInfo().getActiveStatement() != null ) {
                tree_cell.setBackgroundNonSelectionColor(LIGHT_BLUE_COLOR);

            } else {
                tree_cell.setBackgroundNonSelectionColor(Color.white);
            }
	    if (sel) tree_cell.setBackground(DARK_BLUE_COLOR);

	    tree_cell.setFont(tree.getFont());
	    tree_cell.setText(nodeText);

	    return tree_cell;
	}
    }

    class ProofTreePopupMenu extends JPopupMenu
	implements ActionListener, ItemListener {

        private static final int ICON_SIZE = 16;
        private static final long serialVersionUID = -8905927848074190941L;
        private JMenuItem expandAll   = new JMenuItem("Expand All", IconFactory.plus(ICON_SIZE));
	private JMenuItem expandAllBelow   = new JMenuItem("Expand All Below");
	private JMenuItem expandGoals = new JMenuItem("Expand Goals Only", IconFactory.expandGoals(ICON_SIZE));
	private JMenuItem expandGoalsBelow =
		new JMenuItem("Expand Goals Only Below");
	private JMenuItem collapseAll = new JMenuItem("Collapse All", IconFactory.minus(ICON_SIZE));
	private JMenuItem collapseOtherBranches =
		new JMenuItem("Collapse Other Branches");
	private JMenuItem collapseBelow = new JMenuItem("Collapse Below");
	private JMenuItem prevSibling = new JMenuItem("Previous Sibling", IconFactory.previous(ICON_SIZE));
	private JMenuItem nextSibling = new JMenuItem("Next Sibling", IconFactory.next(ICON_SIZE));
	private Map<JCheckBoxMenuItem, ProofTreeViewFilter> filters =
		new LinkedHashMap<JCheckBoxMenuItem, ProofTreeViewFilter> (); // TODO: change to radio button ?
	private JMenuItem notes = new JMenuItem("Edit Notes");
	private JMenuItem search = new JMenuItem("Search", IconFactory.search2(ICON_SIZE));
	private JMenuItem prune    = new JMenuItem("Prune Proof");
	private JMenuItem delayedCut = new JMenuItem("Delayed Cut");
	private JMenuItem runStrategy = new JMenuItem("Apply Strategy",
	    IconFactory.autoModeStartLogo(ICON_SIZE));

	private TreePath path;
	private TreePath branch;
	private Node invokedNode;

	public ProofTreePopupMenu(TreePath p) {
	    super("Choose Action");
	    path = p;
	    delegateView.setSelectionPath(path);
	    if (path.getLastPathComponent() instanceof GUIProofTreeNode) {
		branch = path.getParentPath();
		invokedNode = ((GUIProofTreeNode)path.getLastPathComponent())
			.getNode();
	    } else {
		branch = path;
		invokedNode = ((GUIBranchNode)path.getLastPathComponent())
			.getNode();
	    }
	    create();
	    search.setAccelerator(searchKeyStroke);
	}

	private void create() {
	    // rule application / strategy runs
	    this.add(runStrategy);
	    runStrategy.addActionListener(this);
	    runStrategy.setEnabled(false);
	    if (proof != null) runStrategy.setEnabled(true);

        ProofMacroMenu macroMenu = new ProofMacroMenu(mediator, null);
        if(!macroMenu.isEmpty()) {
            this.add(macroMenu);
        }

	    this.add(prune);
	    if (branch != path) {
		prune.addActionListener(this);
		prune.setIcon(IconFactory.pruneLogo(ICON_SIZE));
		prune.setEnabled(false);
		if (proof != null) {
		    if (proof.isGoal(invokedNode) ||
		        proof.getSubtreeGoals(invokedNode).size()>0) {
		        prune.setEnabled(true);
		    }
		}
	    }

	    if(branch != path){
	        delayedCut.addActionListener(this);
	        delayedCut.setEnabled(false);
	        if (proof != null) {
	            if (!invokedNode.leaf() &&
	                proof.getSubtreeGoals(invokedNode).size()>0) {
	                delayedCut.setEnabled(true);
	            }
	        }
	    }
	    if (de.uka.ilkd.key.proof.delayedcut.DelayedCut.FEATURE.active())
	        this.add(delayedCut);

	    // modifying the node
        this.add(new JSeparator());
        this.add(notes);
        notes.setIcon(IconFactory.editFile(ICON_SIZE));
        notes.addActionListener(this);

	    // modifying the view
	    this.add(new JSeparator());

	    this.add(expandAll);
	    expandAll.addActionListener(this);
	    this.add(expandAllBelow);
	    expandAllBelow.addActionListener(this);
	    this.add(expandGoals);
	    expandGoals.addActionListener(this);
	    this.add(expandGoalsBelow);
	    expandGoalsBelow.addActionListener(this);
	    this.add(collapseAll);
	    collapseAll.addActionListener(this);
	    this.add(collapseOtherBranches);
	    collapseOtherBranches.addActionListener(this);
	    this.add(collapseBelow);
	    collapseBelow.addActionListener(this);
            this.add(new JSeparator());
	    this.add(prevSibling);
	    prevSibling.addActionListener(this);
	    this.add(nextSibling);
	    nextSibling.addActionListener(this);

	    this.add(new JSeparator());
        for (ProofTreeViewFilter filter: ProofTreeViewFilter.ALL) {
            final JCheckBoxMenuItem m = new JCheckBoxMenuItem(filter.name());
            filters.put(m, filter);
            this.add(m);
            m.setSelected(filter.isActive());
            m.addItemListener(this);
        }
	    this.add(search);
	    search.addActionListener(this);
	    this.add(new JSeparator());
	    // disable goals
	    this.add(new SetGoalsBelowEnableStatus(false));
	    // enable goals
	    this.add(new SetGoalsBelowEnableStatus(true));

//	    if (branch != path) {
//                this.add(new JSeparator());
//                JMenu more = new JMenu("More");
//                this.add(more);
//
//		more.add(visualize);
//		more.add(bugdetection);
//		bugdetection.addActionListener(this);
//		bugdetection.setEnabled(true);
//	        more.add(change);
//	    }
	}

	public void actionPerformed(ActionEvent e) {
		if (e.getSource() == delayedCut) {
			delegateModel.setAttentive(false);
			if(mediator().processDelayedCut(invokedNode)){
				delegateModel.updateTree ( null );
			}
			delegateModel.setAttentive(true);
			makeNodeVisible(mediator.getSelectedNode());
		}else
			if (e.getSource() == prune) {
				delegateModel.setAttentive(false);
				mediator().setBack(invokedNode);
				delegateModel.updateTree ( null );
				delegateModel.setAttentive(true);
				makeNodeVisible(mediator.getSelectedNode());
			} else if (e.getSource() == runStrategy) {
				runStrategyOnNode();
			} else if (e.getSource() == expandAll) {
				ExpansionState.expandAll(delegateView);
			} else if (e.getSource() == expandAllBelow) {
				ExpansionState.expandAll(delegateView, branch);
			} else if (e.getSource() == expandGoals) {
				for (final Goal g : proof.openGoals()) {
					makeNodeExpanded ( g.node () );
				}
				collapseClosedNodes ();
				// do not show selected node if it is not on the path to an
				// open goal, but do expand root
				// makeNodeVisible(mediator.getSelectedNode());
				delegateView.expandRow(0);
			} else if (e.getSource() == expandGoalsBelow) {
				expandGoalsBelow();
			} else if (e.getSource() == collapseAll) {
				ExpansionState.collapseAll(delegateView);
				delegateView.expandRow(0);
			} else if (e.getSource() == collapseOtherBranches) {
				collapseOthers(branch);
			} else if (e.getSource() == collapseBelow) {
				collapseBelow();
			} else if (e.getSource() == prevSibling) {
				Object node = branch.getLastPathComponent();
				TreeNode parent = ((GUIAbstractTreeNode) node).getParent();
				if (parent == null) {
					return;
				}
				Object sibling = delegateModel.getChild(parent, delegateModel
						.getIndexOfChild(parent, node) - 1);
				if (!(sibling != null && sibling instanceof GUIBranchNode)) {
					int index = delegateModel
					.getIndexOfChild(parent, node);
					for (int i = parent.getChildCount(); i > index; i--) {
						sibling = delegateModel.getChild(parent, i);
						if (sibling != null && sibling instanceof
								GUIBranchNode) {
							break;
						}
					}
				}
				if (sibling != null && sibling instanceof GUIBranchNode) {
					selectBranchNode((GUIBranchNode)sibling);
				}
			} else if (e.getSource() == nextSibling) {
				Object node = branch.getLastPathComponent();
				TreeNode parent = ((GUIAbstractTreeNode) node).getParent();
				if (parent == null) {
					return;
				}
				Object sibling = delegateModel.getChild(parent, delegateModel
						.getIndexOfChild(parent, node) + 1);
				if (!(sibling != null && sibling instanceof GUIBranchNode)) {
					int index = delegateModel.getIndexOfChild(parent, node);
					for (int i = 0; i < index; i++) {
						sibling = delegateModel.getChild(parent, i);
						if (sibling != null && sibling instanceof
								GUIBranchNode) {
							break;
						}
					}
				}
				if (sibling != null && sibling instanceof GUIBranchNode) {
					selectBranchNode((GUIBranchNode)sibling);
				}
			} else if (e.getSource() == search) {
				showSearchPanel();
			} else if (e.getSource() == notes) {
				openNotes();
			}
	}

	private void openNotes() {
		// display a dialog to attach text to the node
		final Icon editIcon = IconFactory.editFile(20);
		final String origNotes = invokedNode.getNodeInfo().getNotes();
		final String newNotes = (String)JOptionPane.showInputDialog(
				this,null,
				"Annotate this proof node",
				JOptionPane.PLAIN_MESSAGE,
				editIcon,
				null,
				origNotes);
		if (newNotes != null) {
			if (newNotes.length()==0)
				invokedNode.getNodeInfo().setNotes(null);
			else invokedNode.getNodeInfo().setNotes(newNotes);
		}
	}

	private void collapseBelow() {
		Object node = branch.getLastPathComponent();

		for (int count = delegateModel.getChildCount(node), i = 0;
		i < count; i++)
		{
			Object child = delegateModel.getChild(node, i);

			if (!delegateModel.isLeaf(child))
				ExpansionState.collapseAll(delegateView,
						branch.pathByAddingChild(child));
		}
	}

	private void expandGoalsBelow() {
		Object tmpNode = branch.getLastPathComponent();
		if (branch == path) {
			ExpansionState.collapseAll(delegateView, branch);
		} else {
			for ( int count = delegateModel.getChildCount(tmpNode),
					i = 0; i < count; i++ ) {
				Object child = delegateModel.getChild(tmpNode, i);
				if ( !delegateModel.isLeaf ( child ) )
					ExpansionState.collapseAll(delegateView, branch
							.pathByAddingChild(child));
			}
		}
		Iterator<Goal> it = proof.openGoals ().iterator ();
		Node n;
		while ( it.hasNext () ) {
			n = it.next ().node ();
			GUIAbstractTreeNode node = delegateModel.getProofTreeNode(n);
			if (node==null) break;
			TreeNode[] obs=node.getPath();
			TreePath tp = new TreePath(obs);
			if (branch.isDescendant(tp)) {
				delegateView.makeVisible(tp);
			}
		}
	}

	/**
	 * run automatic on the currently selected node.
	 * All enabled goals below the current node are taken into consideration.
	 *
	 * CAUTION: If the node itself is a goal then allow applying rules
	 *   to it even if it were disabled. Desired behaviour?
	 *
	 */
	private void runStrategyOnNode() {
	    Goal invokedGoal = proof.getGoal(invokedNode);
	    // is the node a goal?
            if(invokedGoal == null) {
                ImmutableList<Goal> enabledGoals = proof.getSubtreeEnabledGoals(invokedNode);
                mediator().startAutoMode(enabledGoals);
            } else {
                mediator().startAutoMode(ImmutableSLList.<Goal>nil().prepend(invokedGoal));
            }
	}

	/**
	 * Action for enabling/disabling all goals below "node".
         *
         * @author mulbrich
         */
	private final class SetGoalsBelowEnableStatus extends DisableGoal {

	    /**
         *
         */
        private static final long serialVersionUID = 7264466584742639608L;

        public SetGoalsBelowEnableStatus(boolean enableGoals) {
	        this.enableGoals = enableGoals;

	        String action = enableGoals ? "Automatic" : "Interactive";
	        putValue(NAME, "Set All Goals Below to " + action);
	        if(enableGoals) {
	            putValue(SHORT_DESCRIPTION, "Include this node and all goals in the subtree in automatic rule application");
	            putValue(SMALL_ICON, KEY_HOLE_PULL_DOWN_MENU);
	        } else {
	            putValue(SHORT_DESCRIPTION, "Exclude this node and all goals in the subtree from automatic rule application");
                    putValue(SMALL_ICON, KEY_HOLE_DISABLED_PULL_DOWN_MENU);
	        }
            }

	    /*
	     * return all subgoals of the current node.
	     */
            @Override
            public Iterable<Goal> getGoalList() {
                return proof.getSubtreeGoals(invokedNode);
            }

            /*
             * In addition to marking setting goals, update the tree model
             * so that the label sizes are recalculated
             */
            @Override
            public void actionPerformed(ActionEvent e) {
                super.actionPerformed(e);
                for (final Goal goal : getGoalList()) {
                    delegateModel.updateTree(goal.node());
                }
                // trigger repainting the tree after the completion of this event.
                delegateView.repaint();
            }


	}

	@Override
	public void itemStateChanged(ItemEvent e) {
		final boolean selected = e.getStateChange() == ItemEvent.SELECTED;
		final Object source = e.getSource();
		final ProofTreeViewFilter filter = filters.get(source);
		if (filter==null) return;

		if (!filter.global()) {
			delegateModel.setFilter(filter, selected);

			// enable / disable others
			// TODO: change to radio button and remove this
			for (JCheckBoxMenuItem item: filters.keySet()) {
				if (item != source && !filters.get(item).global()) {
					item.setEnabled(!selected);
				}
			}

			if (branch == path) {
				if (delegateModel.getRoot() instanceof GUIBranchNode) {
					TreeNode node = ((GUIAbstractTreeNode)delegateModel
							.getRoot()).findBranch(invokedNode);
					if (node instanceof GUIBranchNode) {
						selectBranchNode((GUIBranchNode)node);
					}
				}
			} else {
				delegateView.scrollPathToVisible(path);
				delegateView.setSelectionPath(path);
			}
		} else {
			delegateModel.setFilter(filter, selected);
			if (branch == path) {
				if (e.getStateChange() != ItemEvent.SELECTED) {
					if (delegateModel.getRoot() instanceof GUIBranchNode) {
						TreeNode node = ((GUIAbstractTreeNode)delegateModel
								.getRoot()).findBranch(invokedNode);
						if (node instanceof GUIBranchNode) {
							selectBranchNode((GUIBranchNode)node);
						}
					}
				} else {
					if (invokedNode.parent() == null || delegateModel
							.getProofTreeNode(invokedNode.parent())
							.findChild(invokedNode.parent()) == null) {
						// it's still a branch
						if (delegateModel.getRoot() instanceof GUIBranchNode) {
							TreeNode node = ((GUIAbstractTreeNode)delegateModel
									.getRoot()).findBranch(invokedNode);
							if (node instanceof GUIBranchNode) {
								selectBranchNode((GUIBranchNode)node);
							}
						}
					} else {
						TreePath tp = new TreePath(delegateModel.getProofTreeNode(
								invokedNode).getPath());
						delegateView.scrollPathToVisible(tp);
						delegateView.setSelectionPath(tp);
					}
				}
			} else {
				TreePath tp = new TreePath(delegateModel.getProofTreeNode(
						invokedNode).getPath());
				delegateView.scrollPathToVisible(tp);
				delegateView.setSelectionPath(tp);
			}
		}
	}

    }

    // to prevent memory leaks
    private static class CacheLessMetalTreeUI extends MetalTreeUI{

        public void clearDrawingCache(){
            drawingCache.clear();
        }
    }
}
