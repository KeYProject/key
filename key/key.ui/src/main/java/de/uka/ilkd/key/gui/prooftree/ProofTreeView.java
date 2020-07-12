// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
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
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.EventObject;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.WeakHashMap;

import javax.swing.Icon;
import javax.swing.JComponent;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JScrollPane;
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

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.MainWindowTabbedPane;
import de.uka.ilkd.key.gui.NodeInfoVisualizer;
import de.uka.ilkd.key.gui.NodeInfoVisualizerListener;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.nodeviews.TacletInfoToggle;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.util.Debug;

public class ProofTreeView extends JPanel implements TabPanel {

    public static final ColorSettings.ColorProperty GRAY_COLOR =
            ColorSettings.define("[proofTree]gray", "", Color.DARK_GRAY);
    public static final ColorSettings.ColorProperty BISQUE_COLOR =
            ColorSettings.define("[proofTree]bisque", "", new Color(240, 228, 196));
    public static final ColorSettings.ColorProperty LIGHT_BLUE_COLOR =
            ColorSettings.define("[proofTree]lightBlue", "", new Color(230, 254, 255));
    public static final ColorSettings.ColorProperty DARK_BLUE_COLOR =
            ColorSettings.define("[proofTree]darkBlue", "", new Color(31, 77, 153));
    public static final ColorSettings.ColorProperty DARK_GREEN_COLOR =
            ColorSettings.define("[proofTree]darkGreen", "", new Color(0, 128, 51));
    public static final ColorSettings.ColorProperty DARK_RED_COLOR =
            ColorSettings.define("[proofTree]darkRed", "", new Color(191, 0, 0));
    public static final ColorSettings.ColorProperty PINK_COLOR =
            ColorSettings.define("[proofTree]pink", "", new Color(255, 0, 240));
    public static final ColorSettings.ColorProperty ORANGE_COLOR =
            ColorSettings.define("[proofTree]orange", "", new Color(255, 140, 0));

    /**
     * KeYStroke for the search panel: STRG+SHIFT+F
     */
    public final static KeyStroke searchKeyStroke = KeyStroke.getKeyStroke(KeyEvent.VK_F,
            java.awt.event.InputEvent.CTRL_DOWN_MASK
                    | java.awt.event.InputEvent.SHIFT_DOWN_MASK
                    | Toolkit.getDefaultToolkit().getMenuShortcutKeyMask());

    private static final long serialVersionUID = 3732875161168302809L;
    // Taclet info can be shown for inner nodes.
    public final TacletInfoToggle tacletInfoToggle = new TacletInfoToggle();

    private ProofTreePopupFactory proofTreePopupFactory = new ProofTreePopupFactory();


    /**
     * The JTree that is used for actual display and interaction
     */
    final JTree delegateView;

    /**
     * the model that is displayed by the delegateView
     */
    GUIProofTreeModel delegateModel;

    /**
     * the mediator is stored here
     */
    private KeYMediator mediator;
    private WeakHashMap<Proof, GUIProofTreeModel> models = new WeakHashMap<Proof, GUIProofTreeModel>(20);
    /**
     * the proof this view shows
     */
    private Proof proof;
    /**
     * the expansion state of the proof tree
     */
    private ExpansionState expansionState;
    /**
     * listener
     */
    private GUIProofTreeProofListener proofListener;
    private GUITreeSelectionListener treeSelectionListener;
    private GUIProofTreeGUIListener guiListener;

    /**
     * Updates relevant nodes in the proof tree whenever a {@link NodeInfoVisualizer}
     * is opened or closed.
     */
    private NodeInfoVisualizerListener nodeInfoVisListener = new NodeInfoVisualizerListener() {

        @Override
        public void visualizerUnregistered(NodeInfoVisualizer vis) {
            if (vis.getNode().proof() != null
                    && !vis.getNode().proof().isDisposed()
                    && vis.getNode().proof() == proof) {
                delegateModel.updateTree(vis.getNode());
            }
        }

        @Override
        public void visualizerRegistered(NodeInfoVisualizer vis) {
            delegateModel.updateTree(vis.getNode());
        }
    };

    private ConfigChangeListener configChangeListener = new ConfigChangeListener() {
        @Override
        public void configChanged(ConfigChangeEvent e) {
            setProofTreeFont();
        }
    };
    /**
     * Roots of subtrees containing all nodes to which rules have been
     * applied; this is used when auto mode is active
     */
    private ImmutableList<Node> modifiedSubtrees = null;
    private HashSet<Node> modifiedSubtreesCache = null;
    /**
     * the search dialog
     */
    private ProofTreeSearchBar proofTreeSearchPanel;
    private int iconHeight = 12;

    /**
     * creates a new proof tree
     */
    public ProofTreeView(KeYMediator m) {
        this();
        setMediator(m);
    }

    /**
     * creates a new proof tree
     */
    public ProofTreeView() {
        proofListener = new GUIProofTreeProofListener();
        guiListener = new GUIProofTreeGUIListener();
        delegateView = new JTree(
                new DefaultMutableTreeNode("No proof loaded")) {
            private static final long serialVersionUID = 6555955929759162324L;

            @Override
            public void setFont(Font font) {
                iconHeight = font.getSize();
                super.setFont(font);
            }

            @Override
            public void updateUI() {
                super.updateUI();
                /* we want plus/minus signs to expand/collapse tree nodes */
                final TreeUI ui = getUI();
                if (ui instanceof BasicTreeUI) {
                    final BasicTreeUI treeUI = (BasicTreeUI) ui;
                    treeUI.setExpandedIcon(IconFactory.expandedIcon(iconHeight));
                    treeUI.setCollapsedIcon(IconFactory.collapsedIcon(iconHeight));
                }
                if (ui instanceof CacheLessMetalTreeUI) {
                    ((CacheLessMetalTreeUI) ui).clearDrawingCache();
                }
            }
        };
        iconHeight = delegateView.getFontMetrics(delegateView.getFont()).getHeight();
        delegateView.setUI(new CacheLessMetalTreeUI());

        delegateView.getInputMap(JComponent.WHEN_FOCUSED).getParent()
                .remove(KeyStroke.getKeyStroke(KeyEvent.VK_UP, InputEvent.CTRL_MASK));
        delegateView.getInputMap(JComponent.WHEN_FOCUSED).getParent()
                .remove(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, InputEvent.CTRL_MASK));

        delegateView.setInvokesStopCellEditing(true);
        delegateView.getSelectionModel()
                .setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        treeSelectionListener = new GUITreeSelectionListener();
        delegateView.addTreeSelectionListener(treeSelectionListener);
        delegateView.setScrollsOnExpand(true);
        ToolTipManager.sharedInstance().registerComponent(delegateView);

        MouseListener ml = new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                if (e.isPopupTrigger()) {
                    TreePath selPath = delegateView.getPathForLocation
                            (e.getX(), e.getY());
                    if (selPath != null && (selPath.getLastPathComponent()
                            instanceof GUIProofTreeNode ||
                            selPath.getLastPathComponent() instanceof
                                    GUIBranchNode)) {
                        delegateView.setSelectionPath(selPath);
                        JPopupMenu popup = proofTreePopupFactory.create(
                                ProofTreeView.this, selPath);
                        popup.show(e.getComponent(), e.getX(), e.getY());
                    }
                }
            }

            @Override
            public void mouseReleased(MouseEvent e) {
                mousePressed(e);
            }
        };

        delegateView.addMouseListener(ml);

        NodeInfoVisualizer.addListener(nodeInfoVisListener);
        Config.DEFAULT.addConfigChangeListener(configChangeListener);

        setProofTreeFont();
        delegateView.setLargeModel(true);

        setLayout(new BorderLayout());

        JPanel bottomPanel = new JPanel();
        bottomPanel.setLayout(new BorderLayout());
        bottomPanel.add(tacletInfoToggle, BorderLayout.NORTH);
        proofTreeSearchPanel = new ProofTreeSearchBar(this);
        bottomPanel.add(proofTreeSearchPanel, BorderLayout.SOUTH);

        add(new JScrollPane(delegateView), BorderLayout.CENTER);
        add(bottomPanel, BorderLayout.SOUTH);

        layoutKeYComponent();

        final ActionListener keyboardAction = (ActionEvent e) ->
                showSearchPanel();

        registerKeyboardAction(keyboardAction,
                searchKeyStroke,
                JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        KeYGuiExtensionFacade.installKeyboardShortcuts(mediator, this,
                KeYGuiExtension.KeyboardShortcuts.PROOF_TREE_VIEW);
    }

    @Override
    protected void finalize() throws Throwable {
        super.finalize();
        Config.DEFAULT.removeConfigChangeListener(configChangeListener);
        NodeInfoVisualizer.removeListener(nodeInfoVisListener);
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

    /**
     * layout the component
     */
    protected void layoutKeYComponent() {
        delegateView.setBackground(Color.white);
        ProofRenderer renderer = new ProofRenderer();
        delegateView.setCellRenderer(renderer);
        delegateView.putClientProperty("JTree.lineStyle", "Angled");
        delegateView.setVisible(true);
    }

    /**
     * returns the mediator to communicate with the model
     *
     * @return the mediator to communicate with the model
     */
    public KeYMediator getMediator() {
        return mediator;
    }

    /**
     * sets the mediator to communicate with the model
     */
    private void setMediator(KeYMediator m) {
        assert m != null;
        if (mediator != null) {
            unregister();
        }
        mediator = m;
        register();

        Proof selProof = mediator.getSelectedProof();
        if (selProof != null) {
            setProof(selProof);
        }
    }

    private void register() {
        mediator.addKeYSelectionListener(proofListener);
        // This method delegates the request only to the UserInterfaceControl which implements the functionality.
        // No functionality is allowed in this method body!
        mediator.getUI().getProofControl().addAutoModeListener(proofListener);
        mediator.addGUIListener(guiListener);
    }

    private void unregister() {
        mediator.removeKeYSelectionListener(proofListener);
        // This method delegates the request only to the UserInterfaceControl which implements the functionality.
        // No functionality is allowed in this method body!
        mediator.getUI().getProofControl().removeAutoModeListener(proofListener);
        mediator.removeGUIListener(guiListener);
    }

    public boolean selectAbove() {
        return selectRelative(+1);
    }
    public boolean selectBelow() {
        return selectRelative(-1);
    }

    private boolean selectRelative(int i) {
        TreePath path = delegateView.getSelectionPath();
        int row = delegateView.getRowForPath(path);
        TreePath newPath = delegateView.getPathForRow(row-i);
        if (newPath != null) {
            delegateView.setSelectionPath(newPath);
            return true;
        }
        return false;
    }


    // This method is probably responsible for #1509.
    // It deregisters the component from mediator and other services.
    // This is bad since the docking framework may detach and reattach
    // components during the runtime.
//    @Override
//    public void removeNotify() {
//        unregister();
//        try {
//            delegateModel.unregister();
//        } catch (NullPointerException e) {
//            Debug.out("Exception thrown by class ProofTreeView at unregister()");
//        }
//        super.removeNotify();
//    }

    /**
     * sets up the proof tree view if a proof has been loaded
     *
     * @param p the Proof that has been loaded
     */
    private void setProof(Proof p) {
        if (delegateModel != null) {
            expansionState.disconnect(delegateView);
            delegateModel.storeExpansionState(
                    expansionState.state(new LinkedHashSet<>()));
            delegateModel.storeSelection(delegateView.getSelectionPath());
            delegateModel.unregister();
            delegateModel.removeTreeModelListener(proofTreeSearchPanel);
        }

        if (proof != null && !proof.isDisposed()) {
            proof.removeRuleAppListener(proofListener);
        }
        proof = p;
        if (proof != null) {
            proof.addRuleAppListener(proofListener);
        }

        if (proof != null) {
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

    public void removeProofs(Proof[] ps) {
        for (final Proof p : ps) {
            models.remove(p);
        }
    }

    /**
     * moves the scope of the tree view to the given node so that it
     * is visible
     */
    public void makeNodeVisible(Node n) {
        if (n == null) {
            return;
        }

        final GUIAbstractTreeNode node = delegateModel.getProofTreeNode(n);
        if (node == null) {
            return;
        }

        TreeNode[] obs = node.getPath();
        TreePath tp = new TreePath(obs);
        treeSelectionListener.ignoreChange = true;
        delegateView.getSelectionModel().setSelectionPath(tp);
        delegateView.scrollPathToVisible(tp);
        delegateView.validate();
        treeSelectionListener.ignoreChange = false;
    }

    protected void makeNodeExpanded(Node n) {
        GUIAbstractTreeNode node = delegateModel.getProofTreeNode(n);
        if (node == null) {
            return;
        }
        TreeNode[] obs = node.getPath();
        TreePath tp = new TreePath(obs);
        delegateView.makeVisible(tp);
    }

    /**
     * Collapse all subtrees that are closed
     */
    protected void collapseClosedNodes() {
        collapseClosedNodesHelp(new TreePath(delegateModel.getRoot()));
    }

    private void collapseClosedNodesHelp(TreePath path) {
        if (!delegateView.isExpanded(path)) {
            return;
        }

        Object node = path.getLastPathComponent();

        if (node instanceof GUIBranchNode &&
                ((GUIBranchNode) node).getNode().isClosed()) {
            delegateView.collapsePath(path);
            return;
        }

        for (int count = delegateModel.getChildCount(node), i = 0;
             i < count;
             i++) {
            Object child = delegateModel.getChild(node, i);
            if (!delegateModel.isLeaf(child)) {
                collapseClosedNodesHelp(path.pathByAddingChild(child));
            }
        }
    }

    /**
     * Collapse all branches which are not below <tt>path</tt>
     */
    protected void collapseOthers(TreePath path) {
        collapseOthersHelp(new TreePath(delegateModel.getRoot()), path);
    }

    private void collapseOthersHelp(TreePath start, TreePath stop) {
        if (!delegateView.isExpanded(start) || start.equals(stop)) {
            return;
        }

        Object node = start.getLastPathComponent();

        if (node instanceof GUIBranchNode &&
                !start.isDescendant(stop)) {
            delegateView.collapsePath(start);
            return;
        }

        for (int count = delegateModel.getChildCount(node), i = 0;
             i < count;
             i++) {
            Object child = delegateModel.getChild(node, i);
            if (!delegateModel.isLeaf(child)) {
                collapseOthersHelp(start.pathByAddingChild(child), stop);
            }
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
    private void addModifiedNode(Node p_node) {
        if (modifiedSubtrees == null) {
            return;
        }

        try {
            if (!modifiedSubtrees.isEmpty()) {
                Node n = p_node;
                while (true) {
                    if (modifiedSubtreesCache.contains(n)) {
                        return;
                    }
                    if (n.root()) {
                        break;
                    }
                    n = n.parent();
                }
            }

            modifiedSubtrees = modifiedSubtrees.prepend(p_node);
        } finally {
            modifiedSubtreesCache.add(p_node);
        }
    }

    public void showSearchPanel() {
        proofTreeSearchPanel.setVisible(true);
    }

    @Override
    public String getTitle() {
        return "Proof";
    }

    @Override
    public Icon getIcon() {
        return IconFactory.PROOF_TREE.get(MainWindowTabbedPane.TAB_ICON_SIZE);
    }

    @Override
    public JComponent getComponent() {
        return this;
    }
    // INNER CLASSES

    // to prevent memory leaks
    private static class CacheLessMetalTreeUI extends MetalTreeUI {

        public void clearDrawingCache() {
            drawingCache.clear();
        }
    }

    // listens to gui events
    class GUIProofTreeGUIListener implements GUIListener,
            java.io.Serializable {

        private static final long serialVersionUID = 4224100114740308297L;

        /**
         * invoked if a frame that wants modal access is opened
         */
        @Override
        public void modalDialogOpened(EventObject e) {
            delegateView.setEnabled(false);
        }

        /**
         * invoked if a frame that wants modal access is closed
         */
        @Override
        public void modalDialogClosed(EventObject e) {
            delegateView.setEnabled(true);
        }

        @Override
        public void shutDown(EventObject e) {

        }
    }

    class GUIProofTreeProofListener implements AutoModeListener,
            RuleAppListener,
            KeYSelectionListener {

        // hack to select Nodes without changing the selection of delegateView
        public boolean ignoreNodeSelectionChange = false;
        /**
         * node of the last known current goal
         */
        private Node lastGoalNode;

        /**
         * makes selected node visible of lastGoalNode
         */
        public void makeSelectedNodeVisible(Node selectedNode) {
            if (selectedNode != null) {
                if (proof != selectedNode.proof()) {
                    return;
                }
                lastGoalNode = selectedNode;
            }

            makeNodeVisible(lastGoalNode);
            delegateView.validate();
        }

        /**
         * focused node has changed
         */
        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
            if (!ignoreNodeSelectionChange) {
                makeSelectedNodeVisible(mediator.getSelectedNode());
            }
        }

        /**
         * the selected proof has changed (e.g. a new proof has been
         * loaded)
         */
        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            Debug.out("ProofTreeView: initialize with new proof");
            lastGoalNode = null;
            setProof(e.getSource().getSelectedProof());
            delegateView.validate();
        }

        /**
         * invoked if automatic application of rules has started
         */
        @Override
        public void autoModeStarted(ProofEvent e) {
            modifiedSubtrees = ImmutableSLList.<Node>nil();
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

        /**
         * invoked if automatic application of rules has stopped
         */
        @Override
        public void autoModeStopped(ProofEvent e) {
            if (mediator.getSelectedProof() == null) {
                return; // no proof (yet)
            }
            delegateView.removeTreeSelectionListener(treeSelectionListener);
            if (delegateModel == null) {
                setProof(mediator.getSelectedProof());
            } else if (modifiedSubtrees != null) {
                for (final Node n : modifiedSubtrees) {
                    delegateModel.updateTree(n);
                }
            }
            if (!delegateModel.isAttentive()) {
                delegateModel.setAttentive(true);
                mediator.addKeYSelectionListener(proofListener);
            }
            makeSelectedNodeVisible(mediator.getSelectedNode());
            delegateView.addTreeSelectionListener(treeSelectionListener);
            delegateView.validate();
            modifiedSubtrees = null;
            modifiedSubtreesCache = null;
        }


        /**
         * invoked when a rule has been applied
         */
        @Override
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

        @Override
        public void valueChanged(TreeSelectionEvent e) {
            if (ignoreChange) {
                return;
            }
            if (e.getNewLeadSelectionPath() == null) {
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
                    ((GUIAbstractTreeNode) e.getNewLeadSelectionPath().
                            getLastPathComponent());
            if (treeNode instanceof GUIBranchNode) {
                selectBranchNode((GUIBranchNode) treeNode);
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
        private Icon keyHole20x20 = IconFactory.keyHole(iconHeight, iconHeight);

        @Override
        public Component getTreeCellRendererComponent(JTree tree,
                                                      Object value,
                                                      boolean sel,
                                                      boolean expanded,
                                                      boolean leaf,
                                                      int row,
                                                      boolean hasFocus) {
            if (proof == null || proof.isDisposed()) {
                // print dummy tree;
                return super.getTreeCellRendererComponent(tree, value, sel,
                        expanded, leaf, row, hasFocus);
            }

            if (value instanceof GUIBranchNode) {
                super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
                setBackgroundNonSelectionColor(BISQUE_COLOR.get());
                if (((GUIBranchNode) value).isClosed()) {
                    // all goals below this node are closed
                    this.setIcon(IconFactory.provedFolderIcon(iconHeight));
                } else {

                    // Find leaf goal for node and check whether this is a linked goal.

                    // TODO (DS): This marks all "folder" nodes as linked that have
                    //            at least one linked child. Check whether this is
                    //            an acceptable behavior.

                    class FindGoalVisitor implements ProofVisitor {
                        private boolean isLinked = false;

                        public boolean isLinked() {
                            return this.isLinked;
                        }

                        @Override
                        public void visit(Proof proof, Node visitedNode) {
                            Goal g;
                            if ((g = proof.getGoal(visitedNode)) != null &&
                                    g.isLinked()) {
                                this.isLinked = true;
                            }
                        }
                    }

                    FindGoalVisitor v = new FindGoalVisitor();

                    proof.breadthFirstSearch(((GUIBranchNode) value).getNode(), v);
                    if (v.isLinked()) {
                        this.setIcon(IconFactory.linkedFolderIcon(iconHeight));
                    }

                }

                return this;
            }

            if (value instanceof GUIOneStepChildTreeNode) {
                super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
                setForeground(GRAY_COLOR.get());
                setIcon(IconFactory.oneStepSimplifier(iconHeight));
                setText(value.toString());
                return this;
            }

            // now GUIProofTreeNode / GUIOneStepSimpTreeNode
            Node node = ((GUIAbstractTreeNode) value).getNode();
            String nodeText = node.serialNr() + ":" + node.name();
            boolean isBranch = false;
            {
                final Node child = ((GUIAbstractTreeNode) value).findChild(node);
                if (child != null && child.getNodeInfo()
                        .getBranchLabel() != null) {
                    isBranch = true;
                    nodeText += ": " + child.getNodeInfo().getBranchLabel();
                }
            }

            DefaultTreeCellRenderer tree_cell =
                    (DefaultTreeCellRenderer) super.getTreeCellRendererComponent
                            (tree, nodeText, sel, expanded, leaf, row, hasFocus);


            if (node.leaf()) {
                Goal goal = proof.getGoal(node);
                if (goal == null || node.isClosed()) {
                    tree_cell.setForeground(DARK_GREEN_COLOR.get());
                    tree_cell.setIcon(IconFactory.keyHoleClosed(iconHeight));
                    ProofTreeView.this.setToolTipText("Closed Goal");
                    tree_cell.setToolTipText("A closed goal");
                } else {
                    if (goal.isLinked()) {
                        tree_cell.setForeground(PINK_COLOR.get());
                        tree_cell.setIcon(IconFactory.keyHoleLinked(iconHeight, iconHeight));
                        ProofTreeView.this.setToolTipText("Linked Goal");
                        tree_cell.setToolTipText("Linked goal - no automatic rule application");
                    } else if (!goal.isAutomatic()) {
                        tree_cell.setForeground(ORANGE_COLOR.get());
                        tree_cell.setIcon(IconFactory.keyHoleInteractive(iconHeight, iconHeight));
                        ProofTreeView.this.setToolTipText("Disabled Goal");
                        tree_cell.setToolTipText("Interactive goal - no automatic rule application");
                    } else {
                        tree_cell.setForeground(DARK_RED_COLOR.get());
                        tree_cell.setIcon(IconFactory.keyHole(iconHeight, iconHeight));
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
                if (notes != null) {
                    tooltipText += ".<br>Notes: " + notes;
                }

                Icon defaultIcon;
                if (NodeInfoVisualizer.hasInstances(node)) {
                    defaultIcon = IconFactory.WINDOW_ICON.get();
                } else if (notes != null) {
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

                tree_cell.setToolTipText("<html>" + tooltipText + "</html>");
            }

            if (node.getNodeInfo().getNotes() != null) {
                tree_cell.setBackgroundNonSelectionColor(ORANGE_COLOR.get());
            } else if (node.getNodeInfo().getActiveStatement() != null) {
                tree_cell.setBackgroundNonSelectionColor(LIGHT_BLUE_COLOR.get());

            } else {
                tree_cell.setBackgroundNonSelectionColor(Color.white);
            }

            if (sel) {
                tree_cell.setBackground(DARK_BLUE_COLOR.get());
            }

            tree_cell.setFont(tree.getFont());
            tree_cell.setText(nodeText);

            return tree_cell;
        }
    }

    public ProofTreePopupFactory getProofTreePopupFactory() {
        return proofTreePopupFactory;
    }
}
