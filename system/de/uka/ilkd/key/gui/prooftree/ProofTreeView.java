// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.prooftree;

import java.awt.*;
import java.awt.event.*;
import java.util.*;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.TreeUI;
import javax.swing.plaf.basic.BasicTreeUI;
import javax.swing.plaf.metal.MetalTreeUI;
import javax.swing.text.Position;
import javax.swing.tree.*;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.configuration.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.util.Debug;

public class ProofTreeView extends JPanel {


    private static final Color PASTEL_COLOR = new Color(255,255,204);
    private static final Color BISQUE_COLOR = new Color(240,228,196);
    private static final Color PALE_RED_COLOR = new Color(255,153,153);
    private static final Color LIGHT_BLUE_COLOR = new Color(230,230,255);

    /** the mediator is stored here */
    private KeYMediator mediator;

    /** The JTree that is used for actual display and interaction */
    private final JTree delegateView;

    /** the model that is displayed by the delegateView */
    private GUIProofTreeModel delegateModel;
    
    private HashMap<Proof, GUIProofTreeModel> models = new HashMap<Proof, GUIProofTreeModel>(20);

    /** the proof this view shows */
    private Proof proof;

    /** the expansion state of the proof tree */
    private ExpansionState expansionState;

    /** listener */
    private GUIProofTreeProofListener proofListener;
    private GUITreeSelectionListener treeSelectionListener;
    private GUIProofTreeGUIListener guiListener;

    /** KeYStroke for the search panel */
    private final static KeyStroke searchKeyStroke = KeyStroke.getKeyStroke(KeyEvent.VK_F3, 0);

    private ConfigChangeListener configChangeListener =  new ConfigChangeListener() {
                                            public void configChanged(ConfigChangeEvent e) {
                                                setProofTreeFont();
                                            }
                                            public void clear(){
                                                Config.DEFAULT.removeConfigChangeListener(this);
                                            }
                                        };
    /**
     * Roots of subtrees containing all nodes to which rules have been
     * applied; this is used when auto mode is active
     */
    private ListOfNode modifiedSubtrees      = null;
    private HashSet<Node>    modifiedSubtreesCache = null;
    
    /** the search dialog */
    private ProofTreeSearchPanel proofTreeSearchPanel;

    /** creates a new proof tree */
    public ProofTreeView (KeYMediator mediator) {

	proofListener = new GUIProofTreeProofListener();
        guiListener = new GUIProofTreeGUIListener();
	delegateView = new JTree(
		     new DefaultMutableTreeNode("No proof loaded")) {
		public void updateUI() {
		    super.updateUI();
		    /* we want plus/minus signs to expand/collapse tree nodes */
		    final TreeUI ui = getUI();
		    if (ui instanceof BasicTreeUI) {
			final BasicTreeUI treeUI = (BasicTreeUI)ui;
			treeUI.setExpandedIcon(IconFactory.expandedIcon());
			treeUI.setCollapsedIcon(IconFactory.collapsedIcon());
		    }
                    if(ui instanceof CacheLessMetalTreeUI){
                        ((CacheLessMetalTreeUI) ui).clearDrawingCache();
                    }
		}
	    };
            
        delegateView.setUI(new CacheLessMetalTreeUI());

        delegateView.getInputMap(JComponent.WHEN_FOCUSED).getParent().remove(KeyStroke.getKeyStroke(KeyEvent.VK_UP, ActionEvent.CTRL_MASK));
        delegateView.getInputMap(JComponent.WHEN_FOCUSED).getParent().remove(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, ActionEvent.CTRL_MASK));
	

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

// 	UIManager.addPropertyChangeListener(
// 	    new PropertyChangeListener() {
// 		    public void propertyChange(PropertyChangeEvent e) {
// 			if (Config.KEY_FONT_PROOF_TREE.
// 			    equals(e.getPropertyName())) {
// 			    setProofTreeFont();
// 			}
// 		    }
// 		});

	Config.DEFAULT.addConfigChangeListener( configChangeListener);

	setProofTreeFont();
	delegateView.setLargeModel(true);

	updateUI();

	this.setLayout(new BorderLayout());
	this.add(new JScrollPane(delegateView), BorderLayout.CENTER);
	this.proofTreeSearchPanel = new ProofTreeSearchPanel();
	this.add(proofTreeSearchPanel, BorderLayout.SOUTH);	
	
	layoutKeYComponent();	
	
	Proof selProof = mediator.getSelectedProof();
	if (selProof != null) {
	    setProof(selProof);
	}
	
	
	final ActionListener keyboardAction = new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
	        proofTreeSearchPanel.setVisible(true);
	    }               
	};
	
	registerKeyboardAction(keyboardAction, 
	        searchKeyStroke,
	                JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
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
	mediator.addRuleAppListener(proofListener);
	mediator.addGUIListener(guiListener);
        Config.DEFAULT.addConfigChangeListener( configChangeListener);
    }

    private void unregister() {
	mediator.removeKeYSelectionListener(proofListener);
	mediator.removeAutoModeListener(proofListener);
	mediator.removeRuleAppListener(proofListener);
	mediator.removeGUIListener(guiListener);
	configChangeListener.clear();
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
                expansionState.state(new HashSet()));
            delegateModel.storeSelection(delegateView.getSelectionPath());
	    delegateModel.unregister();
            delegateModel.removeTreeModelListener(proofTreeSearchPanel);
	}

	proof = p;
        
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
	
        final GUIProofTreeNode node = delegateModel.getProofTreeNode(n);
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
	GUIProofTreeNode node = delegateModel.getProofTreeNode(n);
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
	     mediator ().getUserConstraint ().displayClosed
	     ( ((GUIBranchNode)node).getNode () ) ) {
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
    private void selectBranchNode(GUIBranchNode node) {
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



    // INNER CLASSES 

    // listens to gui events
    class GUIProofTreeGUIListener implements GUIListener,
                                             java.io.Serializable {
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
	    if (!ignoreNodeSelectionChange)
	        makeSelectedNodeVisible(mediator.getSelectedNode());	    
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
	    modifiedSubtrees      = SLListOfNode.EMPTY_LIST;
	    modifiedSubtreesCache = new HashSet<Node>();
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
	    if (proof == e.getSource()) {
	        addModifiedNode(e.getRuleAppInfo().getOriginalNode());
	    }
	}
        
        
    }    

    class GUITreeSelectionListener implements TreeSelectionListener,
                                              java.io.Serializable {
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
	    if (treeNode instanceof GUIProofTreeNode) {		
		Node node = ((GUIProofTreeNode)treeNode).getNode();
		Goal selected = proof.getGoal(node);
		if (selected != null) {
		    mediator.goalChosen(selected);
		} else {
		    mediator.nonGoalNodeChosen(node);
		}
	    } else if (treeNode instanceof GUIBranchNode) {
                selectBranchNode((GUIBranchNode)treeNode);
            }
	    // catching NullPointerException occurring when renaming root node
	    if (treeNode instanceof GUIBranchNode && ((GUIBranchNode)treeNode)
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
	    
            if (!(value instanceof GUIProofTreeNode)) {
		super.getTreeCellRendererComponent
		    (tree, value, sel, expanded, leaf, row, hasFocus);
		setBackgroundNonSelectionColor(BISQUE_COLOR);
		if (value instanceof GUIBranchNode) {
		    if ( mediator ().getUserConstraint ().displayClosed
			 ( ((GUIBranchNode)value).getNode() ) ) {
			// all goals below this node are closed
			this.setIcon(IconFactory.provedFolderIcon());
		    } else if ( ((GUIBranchNode)value).getNode().getBranchSink ()
				.getResetConstraint ().isSatisfiable () ) {
			// a instantiation of the metavariables does
			// exist that makes the remaining goals of
			// this subtree closed
			this.setIcon(IconFactory.closableFolderIcon());			
		    }		    
		}
		return this;
	    }
	    Node node = ((GUIProofTreeNode)value).getNode();
	    String nodeText = node.serialNr()+":"+node.name();
	    boolean isBranch = false;

	    {
                final Node child = ((GUIProofTreeNode)value).findChild( node );
                if ( child != null && child.getNodeInfo()
                    .getBranchLabel () != null ) {
                    nodeText += ": " + child.getNodeInfo().getBranchLabel ();
                    isBranch = true;
                }
            }

	    DefaultTreeCellRenderer tree_cell =  
		(DefaultTreeCellRenderer) super.getTreeCellRendererComponent
		(tree, nodeText, sel, expanded, leaf, row, hasFocus);
		
	    tree_cell.setFont(tree.getFont());	    	    
	    tree_cell.setText(nodeText);            
                                
	    if (node.leaf()) {
		Goal goal = proof.getGoal(node);
		if ( goal == null ||
		     mediator ().getUserConstraint ().displayClosed ( node ) ) {
		    tree_cell.setForeground(Color.green);
		    tree_cell.setIcon(IconFactory.keyHoleClosed(20,20));
		    ProofTreeView.this.setToolTipText("Closed Goal");
		    tree_cell.setToolTipText("A closed goal");
		} else {
		    if ( goal.getClosureConstraint ().isSatisfiable () ) {
			tree_cell.setForeground(Color.blue);
			tree_cell.setIcon(IconFactory.keyHole(20, 20));
			ProofTreeView.this.setToolTipText("Closable Goal");
			tree_cell.setToolTipText("A goal that can be closed");
		    } else {
			tree_cell.setForeground(Color.red);
			ProofTreeView.this.setToolTipText("Open Goal");
			tree_cell.setToolTipText("An open goal");
		    }                                                            
		    tree_cell.setIcon(IconFactory.keyHole(20, 20));
		}
	    } else {
		/*
		if ( node.getBranchSink ().getResetConstraint ().isSatisfiable () )
		    tree_cell.setForeground(Color.blue);
		else
		*/
		tree_cell.setForeground(Color.black);
                String tooltipText = "An inner node of the proof";
                if (node.isReuseCandidate()) {
		   tree_cell.setIcon(IconFactory.reuseLogo());
                } else {
                    Icon defaultIcon;
                    if (node.getNodeInfo().getInteractiveRuleApplication()) {
                        defaultIcon = IconFactory.interactiveAppLogo(16);
                        tooltipText = "An inner node (rule applied by user)";
                    } else {
                        defaultIcon = null;
                    }
                    if (isBranch) {
                        defaultIcon = getOpenIcon();
                        tooltipText = "A branch node with all siblings hidden";
                    }
                    tree_cell.setIcon(defaultIcon);
                }
		tree_cell.setToolTipText(tooltipText);
	    }

            if (node.getReuseSource() != null) {
		tree_cell.setBackgroundNonSelectionColor(PASTEL_COLOR);
                if (!node.getReuseSource().isConnect()) { 
                   tree_cell.setBackgroundNonSelectionColor(PALE_RED_COLOR);
                }
            } else if (node.getNodeInfo().getActiveStatement() != null ) {
                tree_cell.setBackgroundNonSelectionColor(LIGHT_BLUE_COLOR);

            } else {
                tree_cell.setBackgroundNonSelectionColor(Color.white);
            }
	    if (sel) tree_cell.setBackground(Color.blue);
	    
	    return tree_cell;
	}
    }

    class ProofTreePopupMenu extends JPopupMenu 
	implements ActionListener, ItemListener {	
	
	private JMenuItem expandAll   = new JMenuItem("Expand All");
	private JMenuItem expandAllBelow   = new JMenuItem("Expand All Below");
	private JMenuItem expandGoals = new JMenuItem("Expand Goals Only");
	private JMenuItem expandGoalsBelow = 
		new JMenuItem("Expand Goals Only Below");
	private JMenuItem collapseAll = new JMenuItem("Collapse All");
	private JMenuItem collapseOtherBranches = 
		new JMenuItem("Collapse Other Branches");
	private JMenuItem collapseBelow = new JMenuItem("Collapse Below");
	private JMenuItem prevSibling = new JMenuItem("Previous Sibling");
	private JMenuItem nextSibling = new JMenuItem("Next Sibling");
	private JCheckBoxMenuItem hideIntermediate = 
		new JCheckBoxMenuItem("Hide Intermediate Proofsteps");
	private JCheckBoxMenuItem hideClosedSubtrees = 
		new JCheckBoxMenuItem("Hide Closed Subtrees");
	private JMenuItem search = new JMenuItem("Search");
	private JMenuItem goalBack    = new JMenuItem("Prune Proof");
	private JMenuItem runStrategy = new JMenuItem("Apply Strategy",
	    IconFactory.autoModeStartLogo(10));
        private JMenuItem mark        = new JMenuItem("Mark for Re-Use");
        private JMenuItem visualize   = new JMenuItem("Visualize");
        private JMenuItem test        = new JMenuItem("Create Test For Node");
	
        private JMenuItem change      = new JMenuItem("Change This Node");

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
	    this.add(hideIntermediate);
	    hideIntermediate.setSelected(delegateModel
	        .isHidingIntermediateProofsteps());
	    hideIntermediate.addItemListener(this);
	    this.add(hideClosedSubtrees);
	    hideClosedSubtrees.setSelected(delegateModel
	        .hideClosedSubtrees());
	    hideClosedSubtrees.addItemListener(this);
	    this.add(search);
	    search.addActionListener(this);
	    this.add(new JSeparator());
	    this.add(goalBack);
	    if (branch != path) {
		goalBack.addActionListener(this);
		goalBack.setEnabled(false);
	    }
	    this.add(runStrategy);
	    runStrategy.addActionListener(this);
	    runStrategy.setEnabled(false);
	    if (proof != null) {
		//if (proof.getActiveStrategy() != null) {
		runStrategy.setEnabled(true);
		//}
	    }
	    if (branch != path) {
		this.add(visualize);
		visualize.addActionListener(this);
		visualize.setEnabled(true);
		((ProofTreePopupMenu)this).add(test);
		test.addActionListener(this);
		test.setEnabled(true);
		if (proof != null) {
		    if (proof.isGoal(invokedNode) || 
		        proof.getSubtreeGoals(invokedNode).size()>0) {
		        goalBack.setEnabled(true);
		    }
		}
	        this.add(change);
	        change.addActionListener(this);
	        this.add(mark);
	        mark.addActionListener(this);
	    }
	}

	public void actionPerformed(ActionEvent e) {
	    if (e.getSource() == goalBack) {
		delegateModel.setAttentive(false);
		mediator().setBack(invokedNode);
		delegateModel.updateTree ( null );
		delegateModel.setAttentive(true);
		makeNodeVisible(mediator.getSelectedNode());
	    } else if (e.getSource() == runStrategy) {
		mediator().startAutoMode
		    (proof.getSubtreeGoals(invokedNode));
	    } else if (e.getSource() == mark) {
		mediator().mark(invokedNode);
                delegateView.treeDidChange(); // redraw with mark
            } else if (e.getSource() == expandAll) {
		ExpansionState.expandAll(delegateView);
            } else if (e.getSource() == expandAllBelow) {
		ExpansionState.expandAll(delegateView, branch);
            } else if (e.getSource() == expandGoals) {
                for (final Goal g : proof.openGoals()) {
                    final Node n = g.node ();
                    if ( !mediator ().getUserConstraint ().displayClosed ( n ) )
                        makeNodeExpanded ( n );
                }
		collapseClosedNodes ();
		// do not show selected node if it is not on the path to an
		// open goal, but do expand root
		// makeNodeVisible(mediator.getSelectedNode());
                delegateView.expandRow(0);
            } else if (e.getSource() == expandGoalsBelow) {
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
		IteratorOfGoal it = proof.openGoals ().iterator ();
		Node n;
		while ( it.hasNext () ) {
		    n = it.next ().node ();
		    if ( !mediator ().getUserConstraint ().displayClosed ( n ) ) {
			GUIProofTreeNode node = delegateModel.getProofTreeNode(n);
			if (node==null) break;
			TreeNode[] obs=node.getPath();
			TreePath tp = new TreePath(obs);
			if (branch.isDescendant(tp)) {
				delegateView.makeVisible(tp);
			}
		    }
		}
            } else if (e.getSource() == collapseAll) {
		ExpansionState.collapseAll(delegateView);
                delegateView.expandRow(0);
            } else if (e.getSource() == collapseOtherBranches) {
		collapseOthers(branch);
            } else if (e.getSource() == collapseBelow) {
                Object node = branch.getLastPathComponent();

                for (int count = delegateModel.getChildCount(node), i = 0;
                    i < count; i++)
                {
                    Object child = delegateModel.getChild(node, i);

                    if (!delegateModel.isLeaf(child))
                        ExpansionState.collapseAll(delegateView,
                            branch.pathByAddingChild(child));
                }
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
		proofTreeSearchPanel.setVisible(true);
            }  else if (e.getSource() == visualize) {
                new ProofVisTreeView(mediator.visualizeProof().getVisualizationModel());                
            }else if (e.getSource() == test) {
		mediator.generateTestCaseForSelectedNode();
            } else if (e.getSource() == change) {
                mediator.changeNode(invokedNode);
            }
	}

        public void itemStateChanged(ItemEvent e) {
            if (e.getSource() == hideIntermediate) {
                delegateModel.hideIntermediateProofsteps(e.getStateChange()
                    == ItemEvent.SELECTED);
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
            }
            if (e.getSource() == hideClosedSubtrees) {
                delegateModel.setHideClosedSubtrees(e.getStateChange()
                    == ItemEvent.SELECTED);
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

    class ProofTreeSearchPanel extends JPanel implements DocumentListener,
            TreeModelListener {

        private JTextField searchString = new JTextField(20);
        private JButton prev = new JButton("Prev");
        private JButton next = new JButton("Next");
        private JPanel panel = new JPanel();        
        private JButton close = new JButton("Close");
        private int startRow = 0;
        private int currentRow = 0;
        private Position.Bias direction = Position.Bias.Forward;
        private ActionListener closePanel = new ActionListener() {
            public void actionPerformed(ActionEvent actionEvent) {
                setVisible(false);
            }
        };
        private ActionListener search = new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                if (e.getSource() == next) {        
                    direction = Position.Bias.Forward;
                    searchString.requestFocusInWindow();
                } else if (e.getSource() == prev) {
                    direction = Position.Bias.Backward;
                    searchString.requestFocusInWindow();
                } else {
                    // if e.g. called by pressing enter, perform a forward search
                    direction = Position.Bias.Forward;
                }
                searchNext();
            }
        };
   
        public ProofTreeSearchPanel() {
            registerKeyboardAction(closePanel, KeyStroke
                .getKeyStroke(KeyEvent.VK_ESCAPE, 0), JComponent
                .WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
            registerKeyboardAction(search, KeyStroke
                .getKeyStroke(KeyEvent.VK_ENTER, 0), JComponent
                .WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
            searchString.getDocument().addDocumentListener(this);
            prev.addActionListener(search);
            next.addActionListener(search);
            close.addActionListener(closePanel);
            setLayout(new BorderLayout());
            add(searchString, BorderLayout.NORTH);
            panel.setLayout(new BoxLayout(panel, BoxLayout.LINE_AXIS));
            panel.add(Box.createHorizontalGlue());
            panel.add(prev);
            panel.add(next);
            panel.add(Box.createHorizontalGlue());
            panel.add(close);
            add(panel, BorderLayout.SOUTH);
            super.setVisible(false);
        }

        public void setVisible(boolean vis) {
            super.setVisible(vis);
            if (vis) {
                searchString.selectAll();
                searchString.requestFocusInWindow();
            } else {
                delegateView.requestFocusInWindow();
            }
        }

        private synchronized void searchNext() {
            if (cache == null) fillCache();
            if (direction == Position.Bias.Forward) {
                if (currentRow + 1 < cache.size()) {
                    startRow = currentRow + 1;
                } else {
                    startRow = 0;
                }
            } else {
                if (currentRow - 1 >= 0) {
                    startRow = currentRow - 1;
                } else {
                    startRow = cache.size() - 1;
                }
            }
            search();
        }

        private synchronized void search() {
            if (searchString.getText().equals("")) {
                    startRow = 0;
            }
            currentRow = getNextMatch(searchString.getText(),
                startRow, direction);
            GUIAbstractTreeNode node = null;
            TreePath tp = null;
            if (currentRow != -1) {
                node = cache.get(currentRow);
                tp = new TreePath(node.getPath());
            }
            if (node != null && node instanceof GUIBranchNode) {
                selectBranchNode((GUIBranchNode)node);
            } else {
                delegateView.scrollPathToVisible(tp);
                delegateView.setSelectionPath(tp);
            }
        }

        public void changedUpdate(DocumentEvent e) {
            search();
        }

        public void insertUpdate(DocumentEvent e) {
            search();
        }

        public void removeUpdate(DocumentEvent e) {
            search();
        }

        public void treeNodesChanged(TreeModelEvent e) {
            reset();
        }

        public void treeNodesInserted(TreeModelEvent e) {
            reset();
        }

        public void treeNodesRemoved(TreeModelEvent e) {
            reset();
        }

        public void treeStructureChanged(TreeModelEvent e) {
            reset();
        }

        private Vector<GUIAbstractTreeNode> cache;

        public synchronized void reset() {
            cache = null;
        }

        private void fillCache() {
            cache = new Vector<GUIAbstractTreeNode>();
            if (delegateModel.getRoot() != null) {
                cache.add((GUIAbstractTreeNode)delegateModel.getRoot());
                fillCacheHelp((GUIBranchNode)delegateModel.getRoot());
            }
        }

        private void fillCacheHelp(GUIBranchNode branch) {
            if (branch == null) return;
            GUIAbstractTreeNode n;
            for (int i = 0; i < delegateModel.getChildCount(branch); i++) {
                n = (GUIAbstractTreeNode)delegateModel.getChild(branch, i);
                cache.add(n);
                if (n instanceof GUIBranchNode)
                        fillCacheHelp((GUIBranchNode)n);
            }
        }

        private int getNextMatch(String searchString, int startingRow,
                Position.Bias bias) {
            if (cache == null) fillCache();
            String s = searchString.toLowerCase();
            
            if (bias == Position.Bias.Forward) {
                if (startingRow < 0) startingRow = 0;
                for (int i = startingRow; i < cache.size(); i++) {
                    if (containsString(cache.get(i).toString().toLowerCase(),
                            s)) return i;
                }
                for (int i = 0; i < startingRow && i < cache.size(); i++) {
                    if (containsString(cache.get(i).toString().toLowerCase(),
                            s)) return i;
                }
            } else {
                if (startingRow > cache.size() - 1) startingRow = cache.size()
                        - 1;
                for (int i = startingRow; i >= 0; i--) {
                    if (containsString(cache.get(i).toString().toLowerCase(),
                            s)) return i;
                }
                for (int i = cache.size() - 1; i > startingRow && i > 0; i--) {
                    if (containsString(cache.get(i).toString().toLowerCase(),
                            s)) return i;
                }
            }
            return -1;
        }

        /** 
         * returns true if <tt>searchString</tt> is a substring of <tt>string</tt>
         * @param string the String where to search for an occurrence of <tt>searchString</tt>
         * @param searchString the String to be looked for
         * @return true if a match has been found
         */
        private boolean containsString(String string, String searchString) {
            assert string != null && searchString != null;
            return string.indexOf(searchString) != -1;
        }
        
    }
    
    // to prevent memory leaks
    private class CacheLessMetalTreeUI extends MetalTreeUI{
        
        public void clearDrawingCache(){
            drawingCache.clear();
        }
        
    }

}
