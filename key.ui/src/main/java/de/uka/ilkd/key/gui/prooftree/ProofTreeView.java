package de.uka.ilkd.key.gui.prooftree;

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
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.nodeviews.TacletInfoToggle;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.io.consistency.DiskFileRepo;
import de.uka.ilkd.key.util.Debug;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.plaf.TreeUI;
import javax.swing.plaf.basic.BasicTreeUI;
import javax.swing.plaf.metal.MetalTreeUI;
import javax.swing.tree.*;
import java.awt.*;
import java.awt.event.*;
import java.util.List;
import java.util.*;

import static de.uka.ilkd.key.gui.prooftree.Style.*;

public class ProofTreeView extends JPanel implements TabPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofTreeView.class);

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
    public static final KeyStroke searchKeyStroke = KeyStroke.getKeyStroke(KeyEvent.VK_F,
        java.awt.event.InputEvent.CTRL_DOWN_MASK | java.awt.event.InputEvent.SHIFT_DOWN_MASK
                | Toolkit.getDefaultToolkit().getMenuShortcutKeyMask());

    private static final long serialVersionUID = 3732875161168302809L;

    // Taclet info can be shown for inner nodes.
    public final TacletInfoToggle tacletInfoToggle = new TacletInfoToggle();

    private final ProofTreePopupFactory proofTreePopupFactory = new ProofTreePopupFactory();


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

    private final WeakHashMap<Proof, GUIProofTreeModel> models = new WeakHashMap<>(20);

    /**
     * the proof this view shows
     */
    private Proof proof;

    /**
     * the expansion state of the proof tree
     */
    private ProofTreeExpansionState expansionState;

    /**
     * listener
     */
    private GUIProofTreeProofListener proofListener;
    private GUITreeSelectionListener treeSelectionListener;
    private GUIProofTreeGUIListener guiListener;

    /**
     * Updates relevant nodes in the proof tree whenever a {@link NodeInfoVisualizer} is opened or
     * closed.
     */
    private final NodeInfoVisualizerListener nodeInfoVisListener =
        new NodeInfoVisualizerListener() {

            @Override
            public void visualizerUnregistered(NodeInfoVisualizer vis) {
                if (vis.getNode().proof() != null && !vis.getNode().proof().isDisposed()
                        && vis.getNode().proof() == proof) {
                    delegateModel.updateTree(vis.getNode());
                }
            }

            @Override
            public void visualizerRegistered(NodeInfoVisualizer vis) {
                delegateModel.updateTree(vis.getNode());
            }
        };

    private final ConfigChangeListener configChangeListener = e -> setProofTreeFont();

    /**
     * Roots of subtrees containing all nodes to which rules have been applied; this is used when
     * auto mode is active
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
        delegateView = new JTree(new DefaultMutableTreeNode("No proof loaded")) {
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
        delegateView.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        treeSelectionListener = new GUITreeSelectionListener();
        delegateView.addTreeSelectionListener(treeSelectionListener);
        delegateView.setScrollsOnExpand(true);
        ToolTipManager.sharedInstance().registerComponent(delegateView);

        MouseListener ml = new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                if (e.isPopupTrigger()) {
                    TreePath selPath = delegateView.getPathForLocation(e.getX(), e.getY());
                    if (selPath != null
                            && (selPath.getLastPathComponent() instanceof GUIProofTreeNode
                                    || selPath.getLastPathComponent() instanceof GUIBranchNode)) {
                        delegateView.setSelectionPath(selPath);
                        JPopupMenu popup =
                            proofTreePopupFactory.create(ProofTreeView.this, selPath);
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

        // this only has an effect if the row height is set to a constant (see setProofTreeFont())
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

        final ActionListener keyboardAction = (ActionEvent e) -> showSearchPanel();

        registerKeyboardAction(keyboardAction, searchKeyStroke,
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

        /*
         * We set a constant row height for all rows. This increases the performance of JTree, since
         * this way it does have to not calculate the height of each individual row by its content.
         * This is a reasonable optimization since variable row heights are not needed in our case.
         * The greatest benefit is observable when collapsing large branches.
         */
        int rowHeight = delegateView.getFontMetrics(delegateView.getFont()).getHeight();

        if (myFont != null) {
            rowHeight = delegateView.getFontMetrics(myFont).getHeight();
            // set row height before changing the font (since the latter repaints the component)
            delegateView.setRowHeight(rowHeight);

            delegateView.setFont(myFont);
        } else {
            LOGGER.debug("KEY-PROOF_TREE_FONT not available, use standard font.");
            delegateView.setRowHeight(rowHeight);
        }
    }

    private final ProofRenderer renderer = new ProofRenderer();

    public ProofRenderer getRenderer() {
        return renderer;
    }

    /**
     * layout the component
     */
    protected void layoutKeYComponent() {
        delegateView.setBackground(Color.white);
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
        // This method delegates the request only to the UserInterfaceControl which implements the
        // functionality.
        // No functionality is allowed in this method body!
        mediator.getUI().getProofControl().addAutoModeListener(proofListener);
        mediator.addGUIListener(guiListener);
    }

    private void unregister() {
        mediator.removeKeYSelectionListener(proofListener);
        // This method delegates the request only to the UserInterfaceControl which implements the
        // functionality.
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
        TreePath newPath = delegateView.getPathForRow(row - i);
        if (newPath != null) {
            delegateView.setSelectionPath(newPath);
            return true;
        }
        return false;
    }

    /**
     * sets up the proof tree view if a proof has been loaded
     *
     * @param p the Proof that has been loaded
     */
    private void setProof(Proof p) {
        if (delegateModel != null) {
            expansionState.disconnect();
            delegateModel.setExpansionState(expansionState.copyState());
            delegateModel.storeSelection(delegateView.getSelectionPath());
            delegateModel.unregister();
            delegateModel.removeTreeModelListener(proofTreeSearchPanel);
        }

        if (proof != null && !proof.isDisposed()) {
            proof.removeRuleAppListener(proofListener);
        }

        Proof oldProof = proof;
        proof = p;

        if (proof != null) {
            proof.addRuleAppListener(proofListener);
            delegateModel = models.get(p);
            if (delegateModel == null) {
                delegateModel = new GUIProofTreeModel(p);
                models.put(p, delegateModel);
            }
            delegateModel.addTreeModelListener(proofTreeSearchPanel);
            delegateModel.register();
            delegateView.setModel(delegateModel);
            expansionState =
                new ProofTreeExpansionState(delegateView, delegateModel.getExpansionState());
            delegateView.expandRow(0);

            // Redraw the tree in case the ProofTreeViewFilters have changed
            // since the last time the proof was loaded.
            if (oldProof == null || !oldProof.equals(proof)) {
                delegateModel.updateTree(null);
            }

            delegateView.setSelectionPath(delegateModel.getSelection());
            delegateView.scrollPathToVisible(delegateModel.getSelection());
        } else {
            delegateModel = null;
            delegateView
                    .setModel(new DefaultTreeModel(new DefaultMutableTreeNode("No proof loaded.")));
            expansionState = null;
        }
        proofTreeSearchPanel.reset();
    }

    public void removeProofs(Proof[] ps) {
        for (final Proof p : ps) {
            models.remove(p);
            mediator.getCurrentlyOpenedProofs().removeElement(p);
        }
    }

    /**
     * moves the scope of the tree view to the given node so that it is visible
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

        if (node instanceof GUIBranchNode && ((GUIBranchNode) node).getNode().isClosed()) {
            delegateView.collapsePath(path);
            return;
        }

        for (int count = delegateModel.getChildCount(node), i = 0; i < count; i++) {
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

        if (node instanceof GUIBranchNode && !start.isDescendant(stop)) {
            delegateView.collapsePath(start);
            return;
        }

        for (int count = delegateModel.getChildCount(node), i = 0; i < count; i++) {
            Object child = delegateModel.getChild(node, i);
            if (!delegateModel.isLeaf(child)) {
                collapseOthersHelp(start.pathByAddingChild(child), stop);
            }
        }
    }

    /**
     * Selects the given Branchnode in the ProofTreeView and displays the first child in the main
     * view.
     */
    void selectBranchNode(GUIBranchNode node) {
        if (node == null) {
            return;
        }
        proofListener.ignoreNodeSelectionChange = true;
        mediator.getSelectionModel().setSelectedNode(node.getNode());
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
     * In auto mode, add a node which has been modified in a way leading to structural changes of
     * the proof tree
     */
    private void addModifiedNode(Node pNode) {
        if (modifiedSubtrees == null) {
            return;
        }

        try {
            if (!modifiedSubtrees.isEmpty()) {
                Node n = pNode;
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

            modifiedSubtrees = modifiedSubtrees.prepend(pNode);
        } finally {
            modifiedSubtreesCache.add(pNode);
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

    public GUIProofTreeModel getDelegateModel() {
        return delegateModel;
    }
    // INNER CLASSES

    // to prevent memory leaks
    private static class CacheLessMetalTreeUI extends MetalTreeUI {

        public void clearDrawingCache() {
            drawingCache.clear();
        }
    }

    // listens to gui events
    class GUIProofTreeGUIListener implements GUIListener, java.io.Serializable {

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

    class GUIProofTreeProofListener
            implements AutoModeListener, RuleAppListener, KeYSelectionListener {

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
         * the selected proof has changed (e.g. a new proof has been loaded)
         */
        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            LOGGER.debug("ProofTreeView: initialize with new proof");
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
                LOGGER.debug("delegateModel is null");
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

    class GUITreeSelectionListener implements TreeSelectionListener, java.io.Serializable {
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
            if (!(e.getNewLeadSelectionPath()
                    .getLastPathComponent() instanceof GUIAbstractTreeNode)) {
                return;
            }

            TreePath newTP = e.getNewLeadSelectionPath();
            delegateModel.storeSelection(newTP);


            GUIAbstractTreeNode treeNode =
                ((GUIAbstractTreeNode) e.getNewLeadSelectionPath().getLastPathComponent());
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
            delegateView.setEditable(
                treeNode instanceof GUIBranchNode && treeNode.getNode().parent() != null);
        }
    }


    public class ProofRenderer extends DefaultTreeCellRenderer implements TreeCellRenderer {
        private final List<Styler<GUIAbstractTreeNode>> stylers = new LinkedList<>();

        public ProofRenderer() {
            stylers.add((style, treeNode) -> closedGoal(style, treeNode));
            stylers.add((style, node) -> oneStepSimplification(style, node));
            stylers.add((style, node) -> renderLeaf(style, node));
            stylers.add((style, treeNode) -> renderNonLeaf(style, treeNode));
            stylers.add((style, treeNode) -> checkNotes(style, treeNode));
        }

        public void add(Styler<GUIAbstractTreeNode> guiAbstractTreeNodeStyler) {
            stylers.add(0, guiAbstractTreeNodeStyler);
        }

        private void closedGoal(Style style, GUIAbstractTreeNode treeNode) {
            try {
                GUIBranchNode node = ((GUIBranchNode) treeNode);

                style.set(KEY_ICON, getIcon());
                if (node.isClosed()) {
                    // all goals below this node are closed
                    style.set(KEY_ICON, IconFactory.provedFolderIcon(iconHeight));
                } else {
                    // Find leaf goal for node and check whether this is a linked goal.

                    // DS: This marks all "folder" nodes as linked that have
                    // at least one linked child. Check whether this is
                    // an acceptable behavior.
                    class FindGoalVisitor implements ProofVisitor {
                        private boolean isLinked = false;

                        public boolean isLinked() {
                            return this.isLinked;
                        }

                        @Override
                        public void visit(Proof proof, Node visitedNode) {
                            Goal g;
                            if ((g = proof.getGoal(visitedNode)) != null && g.isLinked()) {
                                this.isLinked = true;
                            }
                        }
                    }
                    FindGoalVisitor v = new FindGoalVisitor();
                    proof.breadthFirstSearch(node.getNode(), v);
                    if (v.isLinked()) {
                        style.set(KEY_ICON, IconFactory.linkedFolderIcon(iconHeight));
                    }
                }
            } catch (ClassCastException ignored) {
            }
        }

        private void renderLeaf(Style style, GUIAbstractTreeNode node) {
            try {
                if (!node.getNode().leaf() || node instanceof GUIBranchNode)
                    return;
                Node leaf = node.getNode();
                Goal goal = proof.getGoal(leaf);
                String toolTipText;
                final String notes = leaf.getNodeInfo().getNotes();

                if (goal == null || leaf.isClosed()) {
                    style.setAndSeal(KEY_COLOR_FOREGROUND, DARK_GREEN_COLOR.get());
                    style.set(KEY_ICON, IconFactory.keyHoleClosed(iconHeight));
                    ProofTreeView.this.setToolTipText("Closed Goal");
                    toolTipText = "A closed goal";
                } else if (goal.isLinked()) {
                    style.set(KEY_COLOR_FOREGROUND, PINK_COLOR.get());
                    style.set(KEY_ICON, IconFactory.keyHoleLinked(20, 20));
                    ProofTreeView.this.setToolTipText("Linked Goal");
                    toolTipText = "Linked goal - no automatic rule application";
                } else if (!goal.isAutomatic()) {
                    style.set(KEY_COLOR_FOREGROUND, ORANGE_COLOR.get());
                    style.set(KEY_ICON, IconFactory.keyHoleInteractive(20, 20));
                    ProofTreeView.this.setToolTipText("Disabled Goal");
                    toolTipText = "Interactive goal - no automatic rule application";
                } else {
                    style.setAndSeal(KEY_COLOR_FOREGROUND, DARK_RED_COLOR.get());
                    style.set(KEY_ICON, IconFactory.keyHole(20, 20));
                    ProofTreeView.this.setToolTipText("Open Goal");
                    toolTipText = "An open goal";
                }
                if (notes != null) {
                    toolTipText += ".\nNotes: " + notes;
                }
                style.set(KEY_TOOLTIP, toolTipText);
            } catch (ClassCastException ignored) {
            }
        }

        private void renderNonLeaf(Style style, GUIAbstractTreeNode treeNode) {
            Node node = treeNode.getNode();
            if (node.leaf() || treeNode instanceof GUIBranchNode)
                return;
            style.set(KEY_COLOR_FOREGROUND, Color.black);
            String tooltipText = "An inner node of the proof";
            final String notes = node.getNodeInfo().getNotes();

            if (notes != null) {
                tooltipText += ".\nNotes: " + notes;
            }

            Icon defaultIcon;
            if (NodeInfoVisualizer.hasInstances(node)) {
                defaultIcon = IconFactory.WINDOW_ICON.get();
            } else if (notes != null) {
                defaultIcon = IconFactory.editFile(16);
            } else if (node.getNodeInfo().getInteractiveRuleApplication()) {
                defaultIcon = IconFactory.interactiveAppLogo(16);
            } else if (node.getNodeInfo().getScriptRuleApplication()) {
                defaultIcon = IconFactory.scriptAppLogo(16);
            } else {
                defaultIcon = null;
            }

            boolean isBranch = false;
            final Node child = treeNode.findChild(node);
            if (child != null && child.getNodeInfo().getBranchLabel() != null) {
                isBranch = true;
                style.set(KEY_TEXT,
                    style.get(KEY_TEXT) + ": " + child.getNodeInfo().getBranchLabel());
            }
            if (isBranch && node.childrenCount() > 1) {
                defaultIcon = getOpenIcon();
                tooltipText = "A branch node with all children hidden";
            }
            style.set(KEY_ICON, defaultIcon);
            style.set(KEY_TOOLTIP, tooltipText);
        }

        private void checkNotes(Style style, GUIAbstractTreeNode treeNode) {
            Node node = treeNode.getNode();
            if (node.getNodeInfo().getNotes() != null) {
                style.set(Style.KEY_COLOR_BACKGROUND, ORANGE_COLOR.get());
            } else {
                if (node.getNodeInfo().getActiveStatement() != null) {
                    style.set(Style.KEY_COLOR_BACKGROUND, LIGHT_BLUE_COLOR.get());
                } else {
                    style.set(Style.KEY_COLOR_BACKGROUND, Color.white);
                }
            }
        }


        private void oneStepSimplification(Style style, GUIAbstractTreeNode node) {
            if (node instanceof GUIOneStepChildTreeNode) {
                style.set(KEY_COLOR_FOREGROUND, GRAY_COLOR.get());
                style.set(KEY_ICON, IconFactory.oneStepSimplifier(16));
                style.set(KEY_TEXT, node.toString());
            }
        }

        @Override
        public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel,
                boolean expanded, boolean leaf, int row, boolean hasFocus) {
            if (proof == null) {
                // print dummy tree
                return super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row,
                    hasFocus);
            }

            super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);

            Style style = new Style();
            style.set(KEY_COLOR_FOREGROUND, getForeground());
            style.set(KEY_COLOR_BACKGROUND, getBackground());
            style.set(KEY_COLOR_BORDER, Color.WHITE);
            style.set(KEY_FONT_BOLD, false);
            style.set(KEY_FONT_ITALIC, false);
            style.set(KEY_TOOLTIP, "");
            style.set(KEY_ICON, null);

            stylers.forEach(it -> it.style(style, (GUIAbstractTreeNode) value));

            setForeground(style.get(KEY_COLOR_FOREGROUND));
            setBackground(style.get(KEY_COLOR_BACKGROUND));

            if (style.get(KEY_COLOR_BORDER) != null) {
                setBorder(BorderFactory.createLineBorder(style.get(KEY_COLOR_BORDER)));
            } else {
                // set default
                setBorder(BorderFactory.createLineBorder(Color.WHITE));
            }

            int fontStyle = (style.getBoolean(KEY_FONT_BOLD) ? Font.BOLD : Font.PLAIN)
                    | (style.getBoolean(KEY_FONT_ITALIC) ? Font.ITALIC : Font.PLAIN);

            setFont(getFont().deriveFont(fontStyle));
            setToolTipText(style.get(KEY_TOOLTIP));
            setIcon(style.get(KEY_ICON));

            return this;
        }
    }


    public ProofTreePopupFactory getProofTreePopupFactory() {
        return proofTreePopupFactory;
    }
}
