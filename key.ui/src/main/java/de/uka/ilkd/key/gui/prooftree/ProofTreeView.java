/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.awt.*;
import java.awt.event.*;
import java.util.*;
import java.util.List;
import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.plaf.TreeUI;
import javax.swing.plaf.basic.BasicTreeUI;
import javax.swing.plaf.metal.MetalTreeUI;
import javax.swing.tree.*;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.NodeInfoVisualizer;
import de.uka.ilkd.key.gui.NodeInfoVisualizerListener;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.rule.RuleApp;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import bibliothek.gui.dock.common.action.CAction;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The proof tree view, showing the nodes of the proof.
 * Usually shown as a tab in the lower left panel.
 */
public class ProofTreeView extends JPanel implements TabPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofTreeView.class);

    public static final ColorSettings.ColorProperty GRAY_COLOR =
        ColorSettings.define("[proofTree]gray", "", Color.DARK_GRAY);
    public static final ColorSettings.ColorProperty LIGHT_BLUE_COLOR =
        ColorSettings.define("[proofTree]lightBlue", "", new Color(230, 254, 255));
    /**
     * Color used for closed goals.
     */
    public static final ColorSettings.ColorProperty DARK_GREEN_COLOR =
        ColorSettings.define("[proofTree]darkGreen", "", new Color(0, 128, 51));
    public static final ColorSettings.ColorProperty DARK_RED_COLOR =
        ColorSettings.define("[proofTree]darkRed", "", new Color(191, 0, 0));
    /**
     * Color used for linked goals.
     */
    public static final ColorSettings.ColorProperty PINK_COLOR =
        ColorSettings.define("[proofTree]pink", "", new Color(255, 0, 240));
    public static final ColorSettings.ColorProperty ORANGE_COLOR =
        ColorSettings.define("[proofTree]orange", "", new Color(255, 140, 0));

    /**
     * KeYStroke for the search panel: STRG+SHIFT+F
     */
    public static final KeyStroke SEARCH_KEY_STROKE = KeyStroke.getKeyStroke(KeyEvent.VK_F,
        KeyStrokeManager.MULTI_KEY_MASK);

    private static final long serialVersionUID = 3732875161168302809L;

    /**
     * Whether to expand oss nodes when using expand all
     */
    private boolean expandOSSNodes = false;

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

    /**
     * Stores for each loaded proof the GUI tree model.
     */
    private final WeakHashMap<Proof, GUIProofTreeModel> models = new WeakHashMap<>(20);
    /**
     * Stores for each loaded proof the position of the scroll view.
     */
    private final WeakHashMap<Proof, Integer> scrollState = new WeakHashMap<>();

    /**
     * The (currently selected) proof this view shows.
     */
    private Proof proof;

    /**
     * the expansion state of the proof tree
     */
    private ProofTreeExpansionState expansionState;

    /**
     * listener
     */
    private final GUIProofTreeProofListener proofListener;
    private final GUITreeSelectionListener treeSelectionListener;
    private final GUIProofTreeGUIListener guiListener;

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
    private final ProofTreeSearchBar proofTreeSearchPanel;

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
                            ProofTreePopupFactory.create(ProofTreeView.this, selPath);
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
        proofTreeSearchPanel = new ProofTreeSearchBar(this);
        bottomPanel.add(proofTreeSearchPanel, BorderLayout.SOUTH);

        add(new JScrollPane(delegateView), BorderLayout.CENTER);
        add(bottomPanel, BorderLayout.SOUTH);

        layoutKeYComponent();

        final ActionListener keyboardAction = (ActionEvent e) -> showSearchPanel();

        registerKeyboardAction(keyboardAction, SEARCH_KEY_STROKE,
            JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        KeYGuiExtensionFacade.installKeyboardShortcuts(mediator, this,
            KeYGuiExtension.KeyboardShortcuts.PROOF_TREE_VIEW);
    }

    public boolean isExpandOSSNodes() {
        return expandOSSNodes;
    }

    public void setExpandOSSNodes(boolean expandOSSNodes) {
        this.expandOSSNodes = expandOSSNodes;
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

            // convert any FontUIResource to Font, so the font is actually updated
            renderer.setFont(myFont.deriveFont((float) myFont.getSize()));
            delegateView.setFont(myFont.deriveFont((float) myFont.getSize()));
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

    /**
     * Select the next goal above the currently selected node.
     *
     * @return whether such a goal was found
     */
    public boolean selectAbove() {
        TreePath path = delegateView.getSelectionPath();
        if (path == null) {
            return false;
        }
        int row = delegateView.getRowForPath(path);
        row--;
        while (delegateView.getPathForRow(row) != null) {
            TreePath tp = delegateView.getPathForRow(row);
            var treeNode = (GUIAbstractTreeNode) tp.getLastPathComponent();
            if (treeNode instanceof GUIBranchNode && treeNode.getNode().parent() != null
                    && treeNode.getNode().parent().childrenCount() > 1
                    && !delegateView.isExpanded(tp)) {
                int prevRows = delegateView.getRowCount();
                delegateView.expandPath(tp);
                int newRows = delegateView.getRowCount();
                // search must continue at the end of the just expanded branch!
                row += (newRows - prevRows);
                continue;
            }
            if (treeNode.getNode().leaf()) {
                mediator.getSelectionModel().setSelectedNode(treeNode.getNode());
                return true;
            }
            row--;
        }
        return false;
    }

    /**
     * Select the next goal below the currently selected node.
     *
     * @return whether such a goal was found
     */
    public boolean selectBelow() {
        TreePath path = delegateView.getSelectionPath();
        if (path == null) {
            return false;
        }
        int row = delegateView.getRowForPath(path);
        row++;
        while (delegateView.getPathForRow(row) != null) {
            TreePath tp = delegateView.getPathForRow(row);
            var treeNode = (GUIAbstractTreeNode) tp.getLastPathComponent();
            if (treeNode instanceof GUIBranchNode && treeNode.getNode().parent() != null
                    && treeNode.getNode().parent().childrenCount() > 1
                    && !delegateView.isExpanded(tp)) {
                delegateView.expandPath(tp);
            }
            if (treeNode.getNode().leaf()) {
                mediator.getSelectionModel().setSelectedNode(treeNode.getNode());
                return true;
            }
            row++;
        }
        return false;
    }

    /**
     * sets up the proof tree view if a proof has been loaded
     *
     * @param p the Proof that has been loaded
     */
    private void setProof(Proof p) {
        if (proof != null) {
            // save old scroll height
            JScrollPane scroller = (JScrollPane) delegateView.getParent().getParent();
            scrollState.put(proof, scroller.getVerticalScrollBar().getValue());
        }
        if (proof == p) {
            return; // proof is already loaded
        }
        ProofTreeViewFilter.NodeFilter filter = null;
        if (delegateModel != null) {
            filter = delegateModel.getActiveNodeFilter();
            expansionState.disconnect();
            delegateModel.setExpansionState(expansionState.copyState());
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

            // Save expansion state to restore:
            // since TreePaths are not valid after refreshing the filter, we need to store the
            // row indices
            List<Integer> rowsToExpand = new ArrayList<>();
            for (TreePath tp : expansionState) {
                rowsToExpand.add(delegateView.getUI().getRowForPath(delegateView, tp));
            }
            Collections.sort(rowsToExpand);

            // Redraw the tree in case the ProofTreeViewFilters have changed
            // since the last time the proof was loaded.
            delegateModel.setFilter(filter, filter != null && filter.isActive());

            // Expand previously visible rows.
            for (int i : rowsToExpand) {
                delegateView.expandRow(i);
            }

            if (delegateModel.getSelection() != null) {
                delegateView.setSelectionPath(delegateModel.getSelection());
                delegateView.scrollPathToVisible(delegateModel.getSelection());
            } else {
                // new proof, select initial node
                delegateView.setSelectionRow(1);
            }

            // Restore previous scroll position.
            JScrollPane scroller = (JScrollPane) delegateView.getParent().getParent();
            Integer i = scrollState.get(proof);
            if (i != null) {
                scroller.getVerticalScrollBar().setValue(i);
            }
        } else {
            delegateModel = null;
            delegateView
                    .setModel(new DefaultTreeModel(new DefaultMutableTreeNode("No proof loaded.")));
            expansionState = null;
        }
        proofTreeSearchPanel.reset();

        for (ProofTreeViewFilter f : ProofTreeViewFilter.ALL) {
            if (f.isActive()) {
                setFilter(f, true);
            }
        }
    }

    public void removeProofs(Proof[] ps) {
        for (final Proof p : ps) {
            models.remove(p);
            scrollState.remove(p);
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

    @Nonnull
    @Override
    public String getTitle() {
        return "Proof";
    }

    @Override
    public Icon getIcon() {
        return IconFactory.PROOF_TREE.get(IconFactory.DEFAULT_SIZE);
    }

    @Nonnull
    @Override
    public JComponent getComponent() {
        return this;
    }

    public boolean setFilter(ProofTreeViewFilter filter, boolean selected) {
        if (delegateModel == null) {
            return false;
        }

        final TreePath selectedPath = delegateModel.getSelection();
        if (selectedPath == null) {
            return false;
        }

        // Save expansion state to restore.
        List<TreePath> rowsToExpand = new ArrayList<>(expansionState);


        final TreePath branch;
        final Node invokedNode;
        if (selectedPath.getLastPathComponent() instanceof GUIProofTreeNode) {
            branch = selectedPath.getParentPath();
            invokedNode =
                ((GUIProofTreeNode) selectedPath.getLastPathComponent()).getNode();
        } else {
            branch = selectedPath;
            invokedNode = ((GUIBranchNode) selectedPath.getLastPathComponent()).getNode();
        }

        if (!filter.global()) {
            delegateModel.setFilter(filter, selected);
            if (branch == selectedPath) {
                if (delegateModel.getRoot() instanceof GUIBranchNode) {
                    TreeNode node = ((GUIAbstractTreeNode) delegateModel.getRoot())
                            .findBranch(invokedNode);
                    if (node instanceof GUIBranchNode) {
                        selectBranchNode((GUIBranchNode) node);
                    }
                }
            } else {
                delegateView.scrollPathToVisible(selectedPath);
                delegateView.setSelectionPath(selectedPath);
            }
        } else {
            delegateModel.setFilter(filter, selected);
            if (branch == selectedPath) {
                if (!selected) {
                    if (delegateModel.getRoot() instanceof GUIBranchNode) {
                        TreeNode node = ((GUIAbstractTreeNode) delegateModel.getRoot())
                                .findBranch(invokedNode);
                        if (node instanceof GUIBranchNode) {
                            selectBranchNode((GUIBranchNode) node);
                        }
                    }
                } else {
                    if (invokedNode.parent() == null || delegateModel
                            .getProofTreeNode(invokedNode.parent())
                            .findChild(invokedNode.parent()) == null) {
                        // it's still a branch
                        if (delegateModel.getRoot() instanceof GUIBranchNode) {
                            TreeNode node =
                                ((GUIAbstractTreeNode) delegateModel.getRoot())
                                        .findBranch(invokedNode);
                            if (node instanceof GUIBranchNode) {
                                selectBranchNode((GUIBranchNode) node);
                            }
                        }
                    } else {
                        TreePath tp = new TreePath(delegateModel
                                .getProofTreeNode(invokedNode).getPath());
                        delegateView.scrollPathToVisible(tp);
                        delegateView.setSelectionPath(tp);
                    }
                }
            } else {
                TreePath tp = new TreePath(
                    delegateModel.getProofTreeNode(invokedNode).getPath());
                delegateView.scrollPathToVisible(tp);
                delegateView.setSelectionPath(tp);
            }
        }

        // Expand previously visible rows.
        for (TreePath tp : rowsToExpand) {
            TreePath newTp = delegateView.getPathForRow(0);
            for (int i = 1; i < tp.getPathCount(); i++) {
                Node n = ((GUIBranchNode) tp.getPathComponent(i)).getNode();
                newTp = newTp.pathByAddingChild(
                    delegateModel.getBranchNode(n, n.getNodeInfo().getBranchLabel()));
            }
            delegateView.expandPath(newTp);
        }
        return true;
    }

    @Nonnull
    @Override
    public Collection<CAction> getTitleCActions() {
        return List.of(ProofTreeSettingsMenuFactory.create(this));
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
            modifiedSubtrees = ImmutableSLList.nil();
            modifiedSubtreesCache = new LinkedHashSet<>();
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
            if (treeNode.getNode().proof().isDisposed()) {
                setProof(null);
                return;
            }
            if (treeNode instanceof GUIBranchNode) {
                selectBranchNode((GUIBranchNode) treeNode);
            } else {
                Node node = treeNode.getNode();
                Goal selected = proof.getOpenGoal(node);
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

    private static String renderTooltip(Style.Tooltip tooltip) {
        String title = tooltip.getTitle();
        List<Style.Tooltip.Fragment> fragments = tooltip.getAdditionalInfos();
        boolean titleEmpty = title == null || title.isEmpty();

        if (fragments.isEmpty() && titleEmpty) {
            return null;
        }

        var result = new StringBuilder();
        result.append("<html>");

        if (!titleEmpty) {
            result.append(title);
        }

        boolean first = titleEmpty;
        for (Style.Tooltip.Fragment fragment : fragments) {
            if (first) {
                first = false;
            } else {
                result.append("<hr>");
            }
            result.append("<b>").append(fragment.key).append("</b>:");
            if (fragment.block) {
                result.append("<br>");
            } else {
                result.append(" ");
            }
            result.append(fragment.value);
        }
        result.append("</html>");
        return result.toString();
    }

    /**
     * Renderer responsible for showing a single node of the proof tree.
     */
    public class ProofRenderer extends DefaultTreeCellRenderer implements TreeCellRenderer {
        private final List<Styler<GUIAbstractTreeNode>> stylers = new LinkedList<>();

        public ProofRenderer() {
            stylers.add(this::render);
        }

        public void add(Styler<GUIAbstractTreeNode> guiAbstractTreeNodeStyler) {
            stylers.add(0, guiAbstractTreeNodeStyler);
        }

        private void render(Style style, GUIAbstractTreeNode node) {
            if (node instanceof GUIBranchNode) {
                renderBranch(style, (GUIBranchNode) node);
            } else if (node instanceof GUIOneStepChildTreeNode) {
                renderOneStepSimplification(style, (GUIOneStepChildTreeNode) node);
            } else if (node.getNode().leaf()) {
                renderLeaf(style, node);
            } else {
                renderNonLeaf(style, node);
            }
            checkNotes(style, node);
        }

        private void renderBranch(Style style, GUIBranchNode node) {
            style.icon = getIcon();

            var text = style.text;
            // Elide text and move it to additional info
            // This does not influence the search since it does not use the text
            if (text.length() > 60) {
                style.text = text.substring(0, 60) + "...";
                style.tooltip.setTitle(text);
            }

            if (node.isClosed()) {
                // all goals below this node are closed
                style.icon = IconFactory.provedFolderIcon(iconHeight);
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
                        if ((g = proof.getOpenGoal(visitedNode)) != null && g.isLinked()) {
                            this.isLinked = true;
                        }
                    }
                }
                FindGoalVisitor v = new FindGoalVisitor();
                proof.breadthFirstSearch(node.getNode(), v);
                if (v.isLinked()) {
                    style.icon = IconFactory.linkedFolderIcon(iconHeight);
                }
            }
        }

        private void renderLeaf(Style style, GUIAbstractTreeNode node) {
            Node leaf = node.getNode();
            Goal goal = proof.getOpenGoal(leaf);
            String toolTipText;

            if (goal == null || leaf.isClosed()) {
                ClosedBy c = leaf.lookup(ClosedBy.class);
                if (c != null) {
                    style.icon = IconFactory.keyCachedClosed(iconHeight, iconHeight);
                } else {
                    style.icon = IconFactory.keyHoleClosed(iconHeight);
                }
                style.foreground = DARK_GREEN_COLOR.get();
                toolTipText = "A closed goal";
                if (c != null) {
                    toolTipText += " (by reference to other proof)";
                }
            } else if (goal.isLinked()) {
                style.foreground = PINK_COLOR.get();
                style.icon = IconFactory.keyHoleLinked(20, 20);
                toolTipText = "Linked goal - no automatic rule application";
            } else if (leaf.lookup(ClosedBy.class) != null) {
                style.foreground = DARK_GREEN_COLOR.get();
                style.icon = IconFactory.keyCachedClosed(iconHeight, iconHeight);
                toolTipText = "Cached goal - reference to another proof";
            } else if (!goal.isAutomatic()) {
                style.foreground = ORANGE_COLOR.get();
                style.icon = IconFactory.keyHoleInteractive(20, 20);
                toolTipText = "Interactive goal - no automatic rule application";
            } else {
                style.foreground = DARK_RED_COLOR.get();
                style.icon = IconFactory.keyHole(20, 20);
                toolTipText = "An open goal";
            }
            String notes = leaf.getNodeInfo().getNotes();
            if (notes != null) {
                style.tooltip.addNotes(notes);
            }
            if (leaf.getNodeInfo().isUselessApplication()) {
                style.tooltip.addAdditionalInfo("Analysis", "Not required to close proof", false);
            }
            style.tooltip.setTitle(toolTipText);
        }

        private void renderNonLeaf(Style style, GUIAbstractTreeNode treeNode) {
            Node node = treeNode.getNode();
            style.foreground = Color.black;

            style.tooltip.addRule(node.getAppliedRuleApp().rule().name().toString());
            PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
            if (pio != null) {
                String on = LogicPrinter.quickPrintTerm(
                    pio.subTerm(), node.proof().getServices());
                style.tooltip.addAppliedOn(on);
            }

            final String notes = node.getNodeInfo().getNotes();
            if (notes != null) {
                style.tooltip.addNotes(notes);
            }

            Icon defaultIcon;
            if (NodeInfoVisualizer.hasInstances(node)) {
                defaultIcon = IconFactory.WINDOW_ICON.get();
            } else if (notes != null) {
                defaultIcon = IconFactory.editFile(16);
            } else if (node.getNodeInfo().isUselessApplication()) {
                defaultIcon = IconFactory.uselessAppLogo(16);
            } else if (node.getNodeInfo().getInteractiveRuleApplication()) {
                defaultIcon = IconFactory.interactiveAppLogo(16);
            } else if (node.getNodeInfo().getScriptRuleApplication()) {
                defaultIcon = IconFactory.scriptAppLogo(16);
            } else {
                defaultIcon = null;
            }

            boolean isBranch = false;
            final Node child = treeNode.findChild(node);
            if (!(treeNode instanceof GUIOneStepChildTreeNode) && child != null
                    && child.getNodeInfo().getBranchLabel() != null) {
                isBranch = true;
                style.text = style.text + ": " + child.getNodeInfo().getBranchLabel();
            }
            if (isBranch && node.childrenCount() > 1) {
                defaultIcon = getOpenIcon();
                style.tooltip.setTitle("A branch node with all children hidden");
            }
            style.icon = defaultIcon;

            var text = style.text;
            // Elide text and move it to additional info
            // This does not influence the search since it does not use the text
            if (text.length() > 60 && treeNode instanceof GUIProofTreeNode) {
                style.text = text.substring(0, 60) + "...";
                // This should only happen if node.name() uses the active statement
                // Pretty print it to make it readable
                style.tooltip.setTitle(node.getAppliedRuleApp().rule().name().toString());
                var active = node.getNodeInfo().getActiveStatement();
                String info = null;
                if (active != null) {
                    PrettyPrinter printer = PrettyPrinter.purePrinter();
                    printer.print(active);
                    info = printer.result();
                }
                info = info == null ? node.name() : info;
                style.tooltip.addAdditionalInfo("Active statement",
                    LogicPrinter.escapeHTML(info, true), true);
            }
        }

        private void checkNotes(Style style, GUIAbstractTreeNode treeNode) {
            Node node = treeNode.getNode();
            // This seems to do nothing at all even though the background color gets set correctly
            if (node.getNodeInfo().getNotes() != null) {
                style.background = ORANGE_COLOR.get();
            } else {
                if (node.getNodeInfo().getActiveStatement() != null) {
                    style.background = LIGHT_BLUE_COLOR.get();
                } else {
                    style.background = Color.white;
                }
            }
        }

        private void renderOneStepSimplification(Style style, GUIOneStepChildTreeNode node) {
            style.foreground = GRAY_COLOR.get();
            style.icon = IconFactory.oneStepSimplifier(16);
            RuleApp app = node.getRuleApp();
            style.text = app.rule().name().toString();
            Services services = node.getNode().proof().getServices();
            String on = LogicPrinter.quickPrintTerm(app.posInOccurrence().subTerm(), services);
            style.tooltip.addRule(style.text);
            style.tooltip.addAppliedOn(on);
        }

        @Override
        public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel,
                boolean expanded, boolean leaf, int row, boolean hasFocus) {
            if (proof == null || proof.isDisposed() || !(value instanceof GUIAbstractTreeNode)) {
                // print dummy tree
                return super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row,
                    hasFocus);
            }

            super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);

            GUIAbstractTreeNode node = (GUIAbstractTreeNode) value;
            Style style = new Style();
            style.foreground = getForeground();
            style.background = getBackground();
            // Normalize whitespace
            style.text = value.toString().replaceAll("\\s+", " ");
            style.border = null;
            style.tooltip = new Style.Tooltip();
            style.icon = null;

            stylers.forEach(it -> it.style(style, node));

            setForeground(style.foreground);
            setBackground(style.background);

            if (style.border != null) {
                setBorder(BorderFactory.createLineBorder(style.border));
            } else {
                // set default
                setBorder(BorderFactory.createLineBorder(Color.WHITE));
            }

            setFont(getFont().deriveFont(Font.PLAIN));
            String tooltip = renderTooltip(style.tooltip);
            setToolTipText(tooltip);
            setText(style.text);
            setIcon(style.icon);

            return this;
        }
    }
}
