/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.prooftree;

import java.util.ArrayList;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.WeakHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;
import javafx.geometry.Insets;
import javafx.scene.control.Button;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.CustomMenuItem;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.control.Tooltip;
import javafx.scene.control.TreeCell;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.input.ContextMenuEvent;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.paint.Color;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.extension.KeYGuiExtensionFacadeF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.nodeinfo.NodeInfoVisualizerF;
import de.uka.ilkd.key.gui.fx.nodeinfo.NodeInfoVisualizerListenerF;
import de.uka.ilkd.key.gui.fx.nodeviews.ProofMacroMenuF;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.FeatureSettings;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * JavaFX version of the proof tree view, the counter-part of
 * {@code de.uka.ilkd.key.gui.prooftree.ProofTreeView} (a Swing {@code JTree} driven by
 * {@code GUIProofTreeModel}) in the module {@code key.ui}.
 * <p>
 * <b>Milestone M2.</b> The layout is a {@link BorderPane} like the Swing view's panel: the tree
 * in the center, the search bar at the bottom (hidden until requested, Swing
 * {@code ProofTreeSearchBar}). The tree structure is built directly from the {@link Proof}: each
 * branch is rendered as a flat list of rule applications (like the Swing model's linear walk),
 * and at a branch point one sub-branch item per child is created, labeled with the branch label
 * of the child (falling back to {@code Case <n>}, mirroring
 * {@code GUIAbstractTreeNode.ensureBranchLabelIsSet}). Leaves are styled by their goal state
 * (open/closed/interactive). Clicking a node selects it in the {@link KeYSelectionModel};
 * selection changes (and proof changes) drive the view.
 * <p>
 * <b>Search</b> (Swing {@code ProofTreeSearchBar}/{@code ProofTreeViewFilter.TreeSearchFilter}):
 * the query (lowercased) is matched against the displayed text {@code serialNr:name} resp. the
 * branch label. With the <em>Collapse</em> toggle active (the default) the tree shows only the
 * subtrees containing a match and, within a branch, hides the non-matching intermediate rule
 * applications; otherwise the full tree is shown and the matching rows are highlighted. Prev/Next
 * cycle through the matches and select them in the selection model; the field gets an alert
 * styling while there is no match. Open with {@code Ctrl+Shift+F}, close with {@code Escape}.
 * <p>
 * Deliberately deferred to later chunks: heatmap, notes/tooltips of the rich
 * Swing renderer, lazy population for very large proofs
 * (currently built eagerly), and incremental per-event tree model updates (live updates currently
 * coalesce into a full rebuild).
 */
public class ProofTreeViewF extends BorderPane implements AutoModeListener {

    private static final Logger LOGGER = LoggerFactory.getLogger(ProofTreeViewF.class);

    private static final KeyCombination OPEN_SEARCH =
        new KeyCodeCombination(KeyCode.F, KeyCombination.CONTROL_DOWN, KeyCombination.SHIFT_DOWN);

    /**
     * One tree entry: either a proof node entry (a rule application), a branch entry (labeled
     * sub-tree; {@code node} is the root of the branch) or a one-step-simplification protocol
     * step of an OSS node entry ({@code node} is the OSS node, {@link #ossRuleApp()} the single
     * rewriting step performed inside the OSS rule).
     */
    public static final class Entry {
        final Node node;
        final String branchLabel;
        final RuleApp ossApp;
        final int ossFormulaNr;

        private Entry(Node node, String branchLabel, RuleApp ossApp, int ossFormulaNr) {
            this.node = node;
            this.branchLabel = branchLabel;
            this.ossApp = ossApp;
            this.ossFormulaNr = ossFormulaNr;
        }

        static Entry node(Node node) {
            return new Entry(node, null, null, -1);
        }

        static Entry branch(Node node, String label) {
            return new Entry(node, Objects.requireNonNull(label), null, -1);
        }

        static Entry oss(Node node, RuleApp app, int formulaNr) {
            return new Entry(node, null, Objects.requireNonNull(app), formulaNr);
        }

        public boolean isBranch() {
            return branchLabel != null;
        }

        /**
         * @return whether this entry is an OSS protocol step of the node entry's applied
         *         {@link OneStepSimplifierRuleApp} (Swing {@code GUIOneStepChildTreeNode})
         */
        public boolean isOssChild() {
            return ossApp != null;
        }

        public Node node() {
            return node;
        }

        /**
         * @return the OSS protocol step of an {@link #isOssChild()} entry, never {@code null} there
         */
        public RuleApp ossRuleApp() {
            return ossApp;
        }

        /** @return the formula number of the OSS application's position in the sequent */
        public int ossFormulaNr() {
            return ossFormulaNr;
        }

        /**
         * @return the text shown for this entry, whitespace-normalized like the Swing renderer
         */
        public String displayText() {
            if (branchLabel != null) {
                return branchLabel;
            }
            if (ossApp != null) {
                return ossApp.rule().name().toString();
            }
            String text = node.serialNr() + ":" + node.name();
            return text.replaceAll("\\s+", " ");
        }
    }

    private final TreeView<Entry> tree = new TreeView<>();

    // -----------------------------------------------------------------------
    // WP-5 — renderer-styling hook (Swing Styler<GUIAbstractTreeNode> parity: the Swing proof
    // tree's renderer holds a list of stylers, e.g. the exploration extension's
    // ExplorationRenderer draws a purple border/background on nodes with ExplorationNodeData,
    // ExplorationExtension.java:128-193). Extensions register a {@link CellStyler} through
    // {@link #addCellStyler(CellStyler)}; the cells consult the stylers on every render.
    // -----------------------------------------------------------------------

    /**
     * The accumulated style of one cell render (Swing {@code de.uka.ilkd.key.gui.prooftree.Style}
     * parity: public fields for the border/background color and the tooltip title). The
     * {@link CellStyler}s accumulate into one shared instance per render; the cell applies
     * {@link #css()} as the inline style and replaces the tooltip text when a title was set.
     */
    public static final class Style {
        private Color border;
        private Color background;
        private String tooltipTitle;

        public Color getBorder() {
            return border;
        }

        public void setBorder(Color border) {
            this.border = border;
        }

        public Color getBackground() {
            return background;
        }

        public void setBackground(Color background) {
            this.background = background;
        }

        public String getTooltipTitle() {
            return tooltipTitle;
        }

        public void setTooltipTitle(String tooltipTitle) {
            this.tooltipTitle = tooltipTitle;
        }

        /**
         * @return the accumulated style as an FX inline style (the Swing renderer draws the
         *         border/background directly; the FX cell maps it onto CSS), empty when no
         *         styler set anything
         */
        public String css() {
            StringBuilder sb = new StringBuilder();
            if (border != null) {
                sb.append("-fx-border-color: ").append(cssColor(border))
                        .append("; -fx-border-width: 1; ");
            }
            if (background != null) {
                sb.append("-fx-background-color: ").append(cssColor(background)).append("; ");
            }
            return sb.toString();
        }

        private static String cssColor(Color color) {
            return String.format("#%02x%02x%02x", (int) Math.round(color.getRed() * 255),
                (int) Math.round(color.getGreen() * 255),
                (int) Math.round(color.getBlue() * 255));
        }
    }

    /**
     * A cell styler of the proof tree (Swing {@code Styler<T>} parity): called for every
     * rendered entry and may set the border/background colors and the tooltip title on the
     * given {@link Style}.
     */
    public interface CellStyler {
        void style(Style style, Entry entry);
    }

    /** the registered stylers (usually at most the one exploration styler; copy-on-write). */
    private final List<CellStyler> cellStylers = new CopyOnWriteArrayList<>();


    private final HBox searchBar = new HBox(4);
    private final TextField searchField = new TextField();
    private final ToggleButton collapseToggle = new ToggleButton("Collapse");

    private KeYSelectionModel selectionModel;
    private Proof proof;
    private boolean updatingSelection;

    /**
     * Coalescing flag for live updates: structural proof events (which can arrive in bursts from
     * the prover thread) schedule at most one refresh.
     */
    private volatile boolean refreshScheduled;

    /** Number of proof tree events observed since the current proof was set (verification). */
    private final AtomicInteger liveEventCount = new AtomicInteger();

    /** Number of coalesced refreshes executed for live events (verification). */
    private final AtomicInteger liveRefreshCount = new AtomicInteger();

    // -----------------------------------------------------------------------
    // P3a: per-proof view state (C19), linearized mode (C20), OSS (C21), auto-mode
    // partial updates (C27)
    // -----------------------------------------------------------------------

    /**
     * C19: the per-proof view state cache (Swing {@code ProofTreeView.viewStates},
     * {@code WeakHashMap<Proof, ProofTreeViewState>}): the expansion set (branch-root nodes),
     * the selected node and the scroll offset of the previously shown proofs. Saved when the
     * displayed proof is switched, restored when a proof is shown again.
     */
    private static final class ViewState {
        final Set<Node> expandedBranches;
        final Node selectedNode;

        ViewState(Set<Node> expandedBranches, Node selectedNode) {
            this.expandedBranches = expandedBranches;
            this.selectedNode = selectedNode;
        }
    }

    private final Map<Proof, ViewState> viewStates = new WeakHashMap<>(4);

    /**
     * C20: linearized proof tree mode (Swing {@code ProofTreeView.linearizedMode}): at a split
     * where the applied rule's last goal template is tagged {@code "main"} the main branch is
     * continued on the same indentation level (Swing {@code GUIBranchNode.fillChildrenCache}).
     * Not persisted (Swing keeps it as a view instance flag).
     */
    private boolean linearizedMode;

    /**
     * C21: whether whole-tree "Expand All" also expands the one-step-simplification protocol
     * children (Swing {@code ProofTreeView.expandOSSNodes}); default {@code false} — OSS nodes
     * stay collapsed and may be expanded manually.
     */
    private boolean expandOSSNodes;

    /**
     * C27: the open goals recorded in {@link #autoModeStarted}; the prover may work on those
     * subtrees, and {@link #autoModeStopped} updates exactly the changed ones (Swing
     * {@code ProofTreeView.modifiedSubtrees}). {@code null} when no auto mode run is pending.
     * Written on the prover thread, read on the FX thread.
     */
    private volatile ImmutableList<Node> modifiedSubtrees;

    /** C27: number of partial (subtree-level) updates executed after auto mode stops. */
    private final AtomicInteger partialUpdateCount = new AtomicInteger();

    /** C27: number of auto mode stops that had to fall back to a full tree rebuild. */
    private final AtomicInteger fullUpdateAfterAutoCount = new AtomicInteger();

    /** C27: if more subtrees changed than this, the whole tree is rebuilt (Swing constant). */
    private static final int MAX_PARTIAL_TREE_UPDATES = 16;

    /** P3a: the mediator and proof control driving the popup strategy/prune actions (C23). */
    private KeYMediatorF mediator;
    private ProofControl proofControl;

    /** the current search query (lowercase), empty if the search is inactive. */
    private String query = "";

    /** the visible items matching {@link #query}, in row order (recomputed after each rebuild). */
    private final List<TreeItem<Entry>> matches = new ArrayList<>();

    /** index into {@link #matches} of the current match, {@code -1} initially. */
    private int matchIndex = -1;

    /**
     * Cache for the "the subtree of this node contains a match" information (Swing
     * {@code TreeSearchFilter.containsMatchCache}); cleared on proof and query changes.
     */
    private final Map<Node, Boolean> containsMatchCache = new HashMap<>();

    /**
     * The registered proof tree filters (reviewer request: factored out of the tree — the
     * context-menu toggles are derived from this list, and a new filter is added with one
     * {@code add(...)} line in {@link #createBuiltinFilters()}). The collapsible search is a
     * different filter type that stays inside the view (it needs the query state).
     * <p>
     * The list is initialized with the built-in filters at field initialization time, because the
     * {@link #contextMenu} field initializer builds the menu (and its filter toggles) from this
     * list before the constructor body runs.
     */
    private final List<ProofTreeFilterF> filters = createBuiltinFilters();

    /**
     * The built-in filter registrations — adding a filter means adding a new
     * {@link ProofTreeFilterF} class and one {@code add(...)} line here.
     *
     * @return the list with the built-in filters (Swing ProofTreeViewFilter checkboxes)
     */
    private static List<ProofTreeFilterF> createBuiltinFilters() {
        List<ProofTreeFilterF> list = new ArrayList<>();
        list.add(new ViewSettingsFilterF("Hide Intermediate Proofsteps",
            ViewSettings::getHideIntermediateProofsteps,
            ViewSettings::setHideIntermediateProofsteps, ViewSettingsFilterF.NODE_FILTER_GROUP));
        list.add(new ViewSettingsFilterF("Hide Non-interactive Proofsteps",
            ViewSettings::getHideAutomodeProofsteps, ViewSettings::setHideAutomodeProofsteps,
            ViewSettingsFilterF.NODE_FILTER_GROUP));
        list.add(new ViewSettingsFilterF("Hide Closed Subtrees",
            ViewSettings::getHideClosedSubtrees, ViewSettings::setHideClosedSubtrees, null));
        list.add(new ViewSettingsFilterF("Hide Subtrees Whose Goals are Interactive",
            ViewSettings::getHideInteractiveGoals, ViewSettings::setHideInteractiveGoals, null));
        return list;
    }

    /**
     * Registers a proof tree filter at runtime (adding a filter = adding a
     * {@link ProofTreeFilterF} class and one registration line).
     *
     * @param filter the filter to register
     * @return this view (fluent)
     */
    public ProofTreeViewF addFilter(ProofTreeFilterF filter) {
        filters.add(filter);
        return this;
    }

    /**
     * The context menu shown on right click: the filter toggles (Swing keeps these checkboxes in
     * the dockable's "Settings" menu, which the FX docking framework does not have yet) plus the
     * expand/collapse and sibling actions of the Swing proof tree popup menu
     * (ProofTreePopupFactory). The state lives in {@link ProofIndependentSettings} like in Swing,
     * so it persists and is shared with the classic UI.
     */
    private final ContextMenu contextMenu = createContextMenu();

    /**
     * C24 (P4): the tail of {@link #contextMenu} holding the PROOF_TREE extension
     * contributions for the last clicked node (a separator plus the contributed items, or
     * nothing); rebuilt in {@link #refreshPopupExtensions()} on every showing.
     */
    private final List<MenuItem> popupExtensionItems = new ArrayList<>();

    /**
     * The branch entry the popup actions apply to, resolved when the menu opens: the selected
     * entry itself if it is a branch, otherwise its parent — like the Swing popup's
     * {@code context.branch}.
     */
    private TreeItem<Entry> popupBranchItem;

    /** the node the popup was invoked on (Swing {@code ProofTreeContext.invokedNode}) */
    private Node popupNode;

    /**
     * C23 (WP-10): the subtree node count captured before the apply-strategy self test started
     * ({@link #verifyApplyStrategyAtNode()}); read back by the worker-thread continuation
     * {@link #verifyApplyStrategyAtNodeResult()}.
     */
    private long applyStrategyNodesBefore;

    /**
     * C23 (WP-10): the strategy step budget of the demo proof, saved while the apply-strategy
     * self test runs with a capped budget ({@link #APPLY_STRATEGY_MAX_STEPS}) and restored by
     * {@link #verifyApplyStrategyAtNodeResult()}.
     */
    private int applyStrategySavedMaxSteps;

    /**
     * C23 (WP-10): the capped strategy step budget of the apply-strategy self test: enough rule
     * applications to grow the clicked node's subtree, few enough to leave open goals below it
     * for the prune part (the core pruner refuses/asserts on fully closed branches,
     * ProofPruner.java:121 with the {@code -ea} runs).
     */
    private static final int APPLY_STRATEGY_MAX_STEPS = 20;

    /**
     * P3b/B12: the "Strategy Macros" submenu of the context menu (Swing
     * {@code ProofTreePopupFactory.initMacroMenu}, ProofTreePopupFactory.java:98-103: a {@code
     * ProofMacroMenu} right after Prune, only when not empty). Persistent (built once in
     * {@link #createContextMenu()}); its items are (re)populated whenever the menu opens or the
     * PROOF_SCRIPTS feature changes ({@link #populateStrategyMacros()}), so every context uses
     * the currently invoked node.
     */
    private Menu strategyMacrosMenu;

    /**
     * D34 (P3c): opens a separate sequent buffer for a proof-tree node, installed by
     * {@code MainWindowF} (Swing {@code SequentViewDock.OpenCurrentNodeAction} creates the dock
     * and adds it to the dock control); {@code null} before the wiring.
     */
    private Consumer<Node> openNodeInSeparateBuffer;

    /**
     * Listens to structural changes of the displayed proof and schedules a coalesced rebuild on
     * the FX thread — the analogue of the Swing view's {@code GUIProofTreeModel} update calls.
     */
    private final ProofTreeListener proofTreeListener = new ProofTreeListener() {
        @Override
        public void proofExpanded(ProofTreeEvent e) {
            handleProofTreeEvent();
        }

        @Override
        public void proofPruned(ProofTreeEvent e) {
            handleProofTreeEvent();
        }

        @Override
        public void proofStructureChanged(ProofTreeEvent e) {
            handleProofTreeEvent();
        }

        @Override
        public void proofClosed(ProofTreeEvent e) {
            handleProofTreeEvent();
        }

        @Override
        public void proofGoalRemoved(ProofTreeEvent e) {
            handleProofTreeEvent();
        }

        @Override
        public void proofGoalsAdded(ProofTreeEvent e) {
            handleProofTreeEvent();
        }

        @Override
        public void proofGoalsChanged(ProofTreeEvent e) {
            handleProofTreeEvent();
        }

        @Override
        public void notesChanged(ProofTreeEvent e) {
            handleProofTreeEvent();
        }
    };

    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        @Override
        public void selectedNodeChanged(KeYSelectionEvent<Node> event) {
            revealSelectedNode();
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
            setProof(event.getSource().getSelectedProof());
        }
    };

    /**
     * WP-2 (NodeInfoVisualizer): updates the affected cells whenever a node-info visualizer
     * (e.g. the origin-term-labels window) is registered or unregistered — Swing
     * {@code ProofTreeView.nodeInfoVisListener} (ProofTreeView.java:150-171) re-renders the
     * affected subtree via {@code delegateModel.updateTree(vis.getNode())}; the FX counterpart
     * re-renders the visible cells (the marker icon of the affected rows re-evaluates
     * {@code NodeInfoVisualizerF.hasInstances}).
     */
    private final NodeInfoVisualizerListenerF nodeInfoVisualizerListener =
        new NodeInfoVisualizerListenerF() {
            @Override
            public void visualizerRegistered(NodeInfoVisualizerF vis) {
                handleNodeInfoVisualizerChange(vis);
            }

            @Override
            public void visualizerUnregistered(NodeInfoVisualizerF vis) {
                handleNodeInfoVisualizerChange(vis);
            }
        };

    private void handleNodeInfoVisualizerChange(NodeInfoVisualizerF vis) {
        Node node = vis.getNode();
        if (node == null || node.proof() == null || proof == null || node.proof() != proof) {
            return;
        }
        FxUtil.runLater(tree::refresh);
    }

    /**
     * Creates an empty proof tree view.
     */
    public ProofTreeViewF() {
        tree.getStyleClass().add("proof-tree");
        tree.setCellFactory(view -> new ProofTreeCell());
        tree.getSelectionModel().selectedItemProperty()
                .addListener((obs, oldItem, newItem) -> handleTreeSelection(newItem));
        // WP-2: the Swing tree is editable and a cell editor denies editing on all nodes except
        // branch nodes whose node has a parent (ProofTreeView.java:243-270, DefaultTreeCellEditor);
        // the F2 key binding of the JTree is the JavaFX TreeViewBehavior default F2 →
        // tree.edit(selectedItem), gated per cell by ProofTreeCell.setEditable
        tree.setEditable(true);
        // WP-2 (NodeInfoVisualizer): the Swing view registers the listener in the constructor and
        // removes it in dispose (ProofTreeView.java:309/:458); the FX view lives for the whole
        // application lifetime, so the listener stays registered
        NodeInfoVisualizerF.addListener(nodeInfoVisualizerListener);
        setCenter(tree);

        createSearchBar();
        setBottom(searchBar);
        searchBar.setVisible(false);
        searchBar.setManaged(false);
        // Swing ProofTreeView registers Ctrl+Shift+F with WHEN_ANCESTOR_OF_FOCUSED_COMPONENT:
        // the shortcut fires whenever the keyboard focus is anywhere inside this view (the key
        // events bubble from the focused control up to this pane).
        setOnKeyPressed(this::handleTreeKeyPressed);
        // the filter toggles and the popup actions live in a right-click menu (Swing exposes
        // them in the dockable's "Settings" menu and the proof tree popup)
        tree.setOnContextMenuRequested(e -> {
            // Swing ProofTreeView.mousePressed (ProofTreeView.java:285-299): the popup is built
            // from the CLICKED row — getPathForLocation(x, y), then setSelectionPath(selPath) —
            // not from the current selection; nothing is shown when the click did not land on a
            // row. The FX counterpart resolves the clicked cell from the event target (the row
            // hit-test of getPathForLocation) and hands it to preparePopup.
            TreeItem<Entry> clicked = clickedItem(e);
            if (clicked != null) {
                preparePopup(clicked);
                contextMenu.show(tree, e.getScreenX(), e.getScreenY());
                e.consume();
            }
        });
    }

    /**
     * @return the tree item under the mouse of a context-request event (the FX counterpart of
     *         Swing's {@code JTree.getPathForLocation(x, y)}): the cell the event targeted, or
     *         {@code null} when the click did not land on a rendered row
     */
    private TreeItem<Entry> clickedItem(ContextMenuEvent e) {
        if (e.getTarget() instanceof TreeCell<?> cell && cell.getTreeView() == tree
                && cell.getIndex() >= 0) {
            return tree.getTreeItem(cell.getIndex());
        }
        return null;
    }

    /**
     * Opens the popup context for the clicked item (extracted from the context-request handler,
     * also driven headlessly by {@link #verifyApplyStrategyAtNode()}): the invoked node is the
     * clicked entry's node, for node entries and branch entries alike (Swing ProofTreeContext),
     * the branch item is its parent for node entries, and — like Swing's
     * {@code setSelectionPath(selPath)} — the selection moves to the clicked row so the popup
     * acts on what the user actually clicked.
     *
     * @param clicked the tree item the popup was invoked on, not {@code null}
     */
    void preparePopup(TreeItem<Entry> clicked) {
        if (tree.getSelectionModel().getSelectedItem() != clicked) {
            tree.getSelectionModel().select(clicked);
        }
        popupNode = clicked.getValue().node();
        TreeItem<Entry> item = clicked;
        if (!item.getValue().isBranch()) {
            item = item.getParent();
        }
        popupBranchItem = item;
    }

    /**
     * Builds the search bar (Swing {@code SearchBar}): a labeled text field, prev/next/close
     * buttons and the Collapse toggle. Live search on every keystroke, {@code Enter} selects the
     * next match, {@code Escape} closes the bar.
     */
    private void createSearchBar() {
        searchBar.getStyleClass().add("proof-tree-search-bar");
        searchBar.setPadding(new Insets(4));

        Button prevButton = new Button();
        prevButton.setGraphic(IconFactoryF.createIcon(IconFactoryF.Key.PREVIOUS));
        prevButton.getStyleClass().add("proof-tree-search-button");
        prevButton.setTooltip(new Tooltip("Previous match"));
        prevButton.setOnAction(e -> searchPrevious());

        Button nextButton = new Button();
        nextButton.setGraphic(IconFactoryF.createIcon(IconFactoryF.Key.NEXT));
        nextButton.getStyleClass().add("proof-tree-search-button");
        nextButton.setTooltip(new Tooltip("Next match"));
        nextButton.setOnAction(e -> searchNext());

        Button closeButton = new Button();
        closeButton.setGraphic(IconFactoryF.createIcon(IconFactoryF.Key.CLOSE));
        closeButton.getStyleClass().add("proof-tree-search-button");
        closeButton.setTooltip(new Tooltip("Close search bar"));
        closeButton.setOnAction(e -> hideSearchBar());

        searchField.getStyleClass().add("proof-tree-search-field");
        searchField.setPromptText("Search proof tree");
        HBox.setHgrow(searchField, Priority.ALWAYS);
        searchField.textProperty().addListener((obs, oldText, newText) -> search());
        searchField.setOnAction(e -> searchNext());
        searchField.setOnKeyPressed(e -> {
            if (KeyCode.ESCAPE.equals(e.getCode())) {
                hideSearchBar();
            }
        });

        collapseToggle.getStyleClass().add("proof-tree-search-collapse");
        collapseToggle.setSelected(true);
        // never truncate the label in a narrow dock (the search bar shares one row)
        collapseToggle.setMinWidth(Region.USE_PREF_SIZE);
        collapseToggle.setTooltip(new Tooltip(
            "Collapse the proof tree to the search matches (otherwise only highlight them)"));
        collapseToggle.setOnAction(e -> search(true));

        searchBar.getChildren().addAll(searchField, prevButton, nextButton, closeButton,
            collapseToggle);
        searchBar.setOnKeyPressed(e -> {
            if (KeyCode.ESCAPE.equals(e.getCode())) {
                hideSearchBar();
            }
        });
    }

    private void handleTreeKeyPressed(KeyEvent event) {
        if (OPEN_SEARCH.match(event)) {
            event.consume();
            showSearchBar();
        }
    }

    /**
     * Registers this view as a selection listener on the given model and shows the currently
     * selected proof, if any.
     *
     * @param model the selection model to observe
     */
    public void attach(KeYSelectionModel model) {
        Objects.requireNonNull(model);
        if (selectionModel == model) {
            return;
        }
        if (selectionModel != null) {
            selectionModel.removeKeYSelectionListener(selectionListener);
        }
        selectionModel = model;
        model.addKeYSelectionListenerChecked(selectionListener);
        setProof(model.getSelectedProof());
        revealSelectedNode();
    }

    /**
     * Shows the given proof, replacing any previously shown tree.
     *
     * @param newProof the proof to display, may be {@code null}
     */
    public void setProof(Proof newProof) {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(() -> setProof(newProof));
            return;
        }
        Proof oldProof = this.proof;
        this.proof = newProof;
        if (oldProof != newProof) {
            // P3a (C19): memorize the view state of the proof we are leaving (expansion,
            // selection; the scroll position is approximated by the selection reveal) — Swing
            // ProofTreeView.setProof stores a ProofTreeViewState per proof and restores it when
            // the proof is shown again
            if (oldProof != null && tree.getRoot() != null) {
                Set<Node> expandedBranches = Collections.newSetFromMap(new IdentityHashMap<>());
                collectExpandedBranches(tree.getRoot(), expandedBranches);
                Node selected = selectionModel != null ? selectionModel.getSelectedNode() : null;
                viewStates.put(oldProof, new ViewState(expandedBranches, selected));
            }
            if (oldProof != null) {
                oldProof.removeProofTreeListener(proofTreeListener);
            }
            if (newProof != null) {
                newProof.addProofTreeListener(proofTreeListener);
            }
            liveEventCount.set(0);
            liveRefreshCount.set(0);
            partialUpdateCount.set(0);
            fullUpdateAfterAutoCount.set(0);
            modifiedSubtrees = null;
            containsMatchCache.clear();
        }
        updatingSelection = true;
        try {
            if (proof == null) {
                tree.setRoot(null);
            } else {
                TreeItem<Entry> root = buildBranch(proof.root(), "Proof Tree");
                tree.setRoot(root);
                root.setExpanded(true);
            }
        } finally {
            updatingSelection = false;
        }
        if (oldProof != newProof && newProof != null) {
            // C19: restore the memorized view state of the proof that is now shown
            ViewState state = viewStates.get(newProof);
            if (state != null && tree.getRoot() != null) {
                applyExpandedBranches(tree.getRoot(), state.expandedBranches);
                if (state.selectedNode != null) {
                    TreeItem<Entry> item = findItem(tree.getRoot(), state.selectedNode);
                    if (item != null && !updatingSelection) {
                        tree.getSelectionModel().select(item);
                        tree.scrollTo(tree.getRow(item));
                    }
                }
            }
            // the current selection model usually already points into the new proof; when it does
            // not (fresh proof), fall back to the default selection
            if (selectionModel != null && selectionModel.getSelectedNode() != null
                    && selectionModel.getSelectedNode().proof() != newProof) {
                selectionModel.defaultSelection();
            }
        }
        updateMatches();
    }

    // ------------------------------------------------------------------
    // WP-5 — renderer-styling hook + filter routing (the seams the exploration port uses;
    // Swing Styler registration: ExplorationExtension.init:128, filter routing:
    // ExplorationModeModel.setShowInteractiveBranches → GUIProofTreeModel.setFilter)
    // ------------------------------------------------------------------

    /**
     * WP-5 — registers a {@link CellStyler} (Swing {@code ProofTreeView.addRenderer} /
     * {@code getRenderer().add(styler)} parity, ProofTreeView.java:1046-1053) and refreshes the
     * tree, so the style applies to the already rendered rows immediately.
     */
    public void addCellStyler(CellStyler styler) {
        cellStylers.add(styler);
        FxUtil.runLater(this::refresh);
    }

    /**
     * WP-5 — removes a previously registered {@link CellStyler}.
     */
    public void removeCellStyler(CellStyler styler) {
        cellStylers.remove(styler);
        FxUtil.runLater(this::refresh);
    }

    /**
     * @return the registered cell stylers (live view; at most one in the shipped UI — the
     *         exploration extension's renderer)
     */
    public List<CellStyler> getCellStylers() {
        return Collections.unmodifiableList(cellStylers);
    }

    /**
     * WP-5 — verification seam of the styling hook: applies the registered stylers to the entry
     * of {@code node} and returns the accumulated style ({@code null} when no styler is
     * registered). The rendered cells apply exactly this style in their {@code updateItem}.
     */
    public Style stylerStyle(Node node) {
        if (cellStylers.isEmpty()) {
            return null;
        }
        Style style = new Style();
        for (CellStyler styler : cellStylers) {
            styler.style(style, Entry.node(node));
        }
        return style;
    }

    /**
     * WP-5 — routes the "Hide justification" toggle of the exploration extension through the
     * {@code HIDE_INTERACTIVE_GOALS} filter (Swing parity:
     * {@code ExplorationModeModel.setShowInteractiveBranches} calls
     * {@code GUIProofTreeModel.setFilter(HIDE_INTERACTIVE_GOALS, …)}, ExplorationModeModel.java
     * :109-114, which rebuilds the tree): the flag is persisted in the shared
     * {@link ViewSettings} (the filter state the context-menu toggle reads back) and the tree is
     * rebuilt with the filter active — hiding the exploration cuts' second (justification)
     * branches whose goals are all interactive.
     *
     * @param active whether subtrees whose goals are all interactive are hidden
     */
    public void applyHideInteractiveGoals(boolean active) {
        setHideInteractiveGoals(active);
        refresh();
    }

    /**
     * Rebuilds the tree from the current proof, preserving the expansion state of the branches
     * and the selection. Used when rule applications changed the proof (live updates), when the
     * search query changed, and by the self tests.
     */
    public void refresh() {
        if (proof == null) {
            setProof(null);
            return;
        }
        Set<Node> expandedBranches = Collections.newSetFromMap(new IdentityHashMap<>());
        collectExpandedBranches(tree.getRoot(), expandedBranches);
        setProof(proof);
        if (tree.getRoot() != null) {
            applyExpandedBranches(tree.getRoot(), expandedBranches);
            revealSelectedNode();
        }
    }

    /**
     * Coalesces structural proof events into at most one scheduled rebuild: events arrive in
     * bursts from the prover thread and a full rebuild of the current proof state covers all of
     * them.
     */
    private void handleProofTreeEvent() {
        liveEventCount.incrementAndGet();
        if (refreshScheduled) {
            return;
        }
        refreshScheduled = true;
        FxUtil.runLater(() -> {
            refreshScheduled = false;
            if (proof == null) {
                return;
            }
            liveRefreshCount.incrementAndGet();
            try {
                refresh();
            } catch (ConcurrentModificationException | IndexOutOfBoundsException e) {
                // the proof was mutated concurrently while the tree was rebuilt; the
                // corresponding structural event schedules another coalesced refresh
                LOGGER.debug("Proof tree refresh raced with proof mutation, retrying", e);
                handleProofTreeEvent();
            }
        });
    }

    /**
     * @return a one-line report about the observed live proof tree events and the executed
     *         coalesced refreshes (for the M2 verification)
     */
    public String getLiveUpdateReport() {
        return "liveEvents=" + liveEventCount.get() + " liveRefreshes=" + liveRefreshCount.get();
    }

    private static void collectExpandedBranches(TreeItem<Entry> item, Set<Node> into) {
        if (item == null) {
            return;
        }
        if (item.isExpanded() && item.getValue() != null && item.getValue().isBranch()) {
            into.add(item.getValue().node());
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            collectExpandedBranches(child, into);
        }
    }

    private static void applyExpandedBranches(TreeItem<Entry> item, Set<Node> expandedBranches) {
        if (item.getValue() != null && item.getValue().isBranch()
                && expandedBranches.contains(item.getValue().node())) {
            item.setExpanded(true);
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            applyExpandedBranches(child, expandedBranches);
        }
    }

    /**
     * Development self-test (M2): verifies that every proof node appears exactly once as a node
     * entry (each node is either on a branch's linear chain or the root of exactly one branch,
     * whose folder is an additional labeled entry like the Swing model's branch nodes).
     *
     * @return a one-line report, {@code "... PASS"} if the structure is consistent
     */
    public String verifyTreeStructure() {
        if (proof == null || tree.getRoot() == null) {
            return "no proof";
        }
        Set<Node> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        int[] counters = { 0, 0, 0 }; // node entries, branch entries, OSS rows
        collect(tree.getRoot(), seen, counters);
        int proofNodeCount = 0;
        for (Iterator<Node> it = proof.root().subtreeIterator(); it.hasNext();) {
            it.next();
            proofNodeCount++;
        }
        boolean pass = seen.size() == proofNodeCount && counters[0] == proofNodeCount;
        boolean filtersActive = hideIntermediateSteps() || hideAutomodeSteps()
                || hideClosedSubtrees() || hideInteractiveGoals();
        if (filtersActive) {
            // with an active filter the displayed tree is intentionally a subset of the proof;
            // consistency means: every displayed entry is a real proof node, without duplicates
            pass = seen.size() == counters[0] + counters[1] && counters[0] <= proofNodeCount;
        }
        return "proofNodes=" + proofNodeCount + " nodeEntries=" + counters[0] + " unique="
            + seen.size() + " branches=" + counters[1] + " ossRows=" + counters[2]
            + (filtersActive ? " filtered" : "") + " " + (pass ? "PASS" : "FAIL");
    }

    /**
     * Development self-test (M2): exercises the search bar like the Swing one — searches a term
     * that matches some rule applications, checks that the collapsed tree only shows matching
     * entries plus branch folders, then restores the full tree.
     *
     * @param queryString the query to search for
     * @return a one-line report, {@code "... PASS"} if the search behaves as expected
     */
    public String verifySearch(String queryString) {
        if (proof == null || tree.getRoot() == null) {
            return "no proof";
        }
        showSearchBar();
        searchField.setText(queryString);
        int matchCount = matches.size();
        int[] counters = { 0, 0, 0 }; // matching node entries, non-matching node entries, branches
        checkCollapsed(tree.getRoot(), counters);
        // within a collapsed branch, the visible node entries must be all matching or all
        // non-matching — a mixture means the chain filter is inconsistent
        boolean collapsedConsistent = counters[0] == 0 || counters[1] == 0;
        // restore the full tree
        hideSearchBar();
        String restored = verifyTreeStructure();
        boolean pass = matchCount > 0 && collapsedConsistent && restored.endsWith("PASS");
        return "query=" + queryString + " matches=" + matchCount + " collapsedNodes=" + counters[0]
            + " nonMatchingNodes=" + counters[1] + " collapsedBranches=" + counters[2]
            + " restored=[" + restored + "] " + (pass ? "PASS" : "FAIL");
    }

    /**
     * Development self-test (M2): exercises the tree filters like the Swing "Settings" menu —
     * counts the entries with every filter off, then with Hide Intermediate Proofsteps, Hide
     * Closed Subtrees and Hide Non-interactive Proofsteps in turn (each must shrink the tree),
     * then restores the baseline. The filter state is left exactly as it was found.
     *
     * @return a one-line report, {@code "... PASS"} if all filter applications shrink the tree
     *         and the baseline is restored
     */
    public String verifyTreeFilters() {
        if (proof == null || tree.getRoot() == null) {
            return "no proof";
        }
        boolean wasIntermediate = hideIntermediateSteps();
        boolean wasAutomode = hideAutomodeSteps();
        boolean wasClosed = hideClosedSubtrees();
        boolean wasInteractive = hideInteractiveGoals();
        setHideIntermediateSteps(false);
        setHideAutomodeSteps(false);
        setHideClosedSubtrees(false);
        setHideInteractiveGoals(false);
        refresh();
        int baseline = countEntries();
        setHideIntermediateSteps(true);
        refresh();
        int intermediate = countEntries();
        setHideIntermediateSteps(false);
        setHideClosedSubtrees(true);
        refresh();
        int closedHidden = countEntries();
        setHideClosedSubtrees(false);
        setHideAutomodeSteps(true);
        refresh();
        int automode = countEntries();
        setHideAutomodeSteps(false);
        refresh();
        int restored = countEntries();
        // restore the persisted state found on entry
        setHideIntermediateSteps(wasIntermediate);
        setHideAutomodeSteps(wasAutomode);
        setHideClosedSubtrees(wasClosed);
        setHideInteractiveGoals(wasInteractive);
        refresh();
        boolean pass = baseline > 0 && intermediate < baseline && closedHidden < baseline
                && automode < baseline && restored == baseline;
        return "baseline=" + baseline + " hideIntermediate=" + intermediate + " hideClosed="
            + closedHidden + " hideAutomode=" + automode + " restored=" + restored + " "
            + (pass ? "PASS" : "FAIL");
    }

    /**
     * prooftree (P3a): self-test of the C19-C22/C25 parity items — the per-proof view state
     * cache, the linearized mode, the OSS protocol rows and the whole-tree expand/collapse —
     * plus the C25 node-filter counting rule. Leaves every state (filters, toggles, expansion)
     * exactly as it was found.
     *
     * @return a one-line report, {@code "... PASS"} if every check passes
     */
    public String verifyProoftreeSemantics() {
        if (proof == null || tree.getRoot() == null) {
            return "no proof";
        }
        List<String> problems = new ArrayList<>();
        boolean wasLinearized = linearizedMode;
        boolean wasExpandOss = expandOSSNodes;
        boolean wasIntermediate = hideIntermediateSteps();
        boolean wasAutomode = hideAutomodeSteps();
        boolean wasClosed = hideClosedSubtrees();
        boolean wasInteractive = hideInteractiveGoals();
        Set<Node> originallyExpanded = Collections.newSetFromMap(new IdentityHashMap<>());
        collectExpandedBranches(tree.getRoot(), originallyExpanded);
        try {
            // baseline: all filters off, both P3a toggles off
            linearizedMode = false;
            expandOSSNodes = false;
            setHideIntermediateSteps(false);
            setHideAutomodeSteps(false);
            setHideClosedSubtrees(false);
            setHideInteractiveGoals(false);
            refresh();
            int baseline = countEntries();
            String structure = verifyTreeStructure();
            if (!structure.endsWith("PASS")) {
                problems.add("baseline structure: " + structure);
            }

            // C20: linearized mode folds "main"-tagged splits into the chain — the entry count
            // must not grow and the structure must stay consistent
            linearizedMode = true;
            refresh();
            int linearized = countEntries();
            String linearizedStructure = verifyTreeStructure();
            linearizedMode = false;
            refresh();
            int restored = countEntries();
            if (linearized > baseline || restored != baseline
                    || !linearizedStructure.endsWith("PASS")) {
                problems.add("linearized baseline=" + baseline + " linear=" + linearized
                    + " restored=" + restored + " [" + linearizedStructure + "]");
            }

            // C21: count the OSS protocol rows in the tree; with "expand OSS nodes" off the
            // whole-tree expand must keep the OSS rows collapsed, on it must expand them
            long ossRows = countOssRows(tree.getRoot());
            long ossNodes = 0;
            long expectedOssRows = 0;
            for (Iterator<Node> it = proof.root().subtreeIterator(); it.hasNext();) {
                Node n = it.next();
                if (n.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp oss
                        && oss.getProtocol() != null) {
                    ossNodes++;
                    // one row per rule application performed inside the step
                    expectedOssRows += oss.getProtocol().size();
                }
            }
            collapseEntireTree();
            expandEntireTree();
            long collapsedOssParents = countExpandedOssParents(tree.getRoot());
            expandOSSNodes = true;
            expandEntireTree();
            long expandedOssParents = countExpandedOssParents(tree.getRoot());
            expandOSSNodes = false;
            // proofs without one-step simplifications vacuous-pass (the demo's stored proof
            // only gains OSS nodes once the strategy applies OneStepSimplifier)
            boolean ossOk = true;
            if (ossNodes > 0) {
                ossOk = ossRows == expectedOssRows && collapsedOssParents == 0
                        && expandedOssParents == ossNodes;
            }
            if (!ossOk) {
                problems.add("oss rows=" + ossRows + " ossNodes=" + ossNodes
                    + " expectedRows=" + expectedOssRows
                    + " expandedParents(off)=" + collapsedOssParents
                    + " expandedParents(on)=" + expandedOssParents);
            }

            // C22: collapse all leaves only the root expanded; expand all expands the whole tree
            // (OSS protocol rows stay collapsed unless the C21 toggle is on — asserted above)
            collapseEntireTree();
            boolean onlyRoot = onlyRootExpanded(tree.getRoot());
            expandEntireTree();
            long expandedRows = countExpandedRows(tree.getRoot());
            long totalRows = countEntries();
            if (!onlyRoot || expandedRows <= 1 || expandedRows > totalRows) {
                problems.add("collapseAll onlyRoot=" + onlyRoot + " expandAll rows="
                    + expandedRows + "/" + totalRows);
            }

            // C25: with "hide intermediate proofsteps" active and no global filter the Swing
            // counting rule keeps exactly the last child of every child list — no node entry may
            // sit before a later sibling
            setHideIntermediateSteps(true);
            refresh();
            boolean nonLastNodeEntries = hasNonLastNodeEntry(tree.getRoot());
            setHideIntermediateSteps(false);
            refresh();
            if (nonLastNodeEntries) {
                problems.add("hideIntermediate counting rule violated (non-last node entry)");
            }

            // C19: switching proofs away and back restores the expanded branches and the
            // selection (view-states cache)
            int[] ossCounters = { 0, 0, 0 };
            collect(tree.getRoot(), Collections.newSetFromMap(new IdentityHashMap<>()),
                ossCounters);
            if (ossCounters[1] > 0) {
                TreeItem<Entry> someBranch = firstBranchItem(tree.getRoot());
                if (someBranch != null) {
                    Node branchNode = someBranch.getValue().node();
                    someBranch.setExpanded(true);
                    Node savedSelection = selectionModel != null
                            ? selectionModel.getSelectedNode()
                            : null;
                    Proof currentProof = this.proof;
                    setProof(null);
                    setProof(currentProof);
                    boolean branchRestored = isBranchExpanded(branchNode);
                    boolean selectionRestored = savedSelection != null
                            && selectionModel != null
                            && selectionModel.getSelectedNode() == savedSelection;
                    if (!branchRestored || !selectionRestored) {
                        problems.add("view-state restore branch=" + branchRestored
                            + " selection=" + selectionRestored);
                    }
                }
            }
        } finally {
            // restore the state found on entry
            linearizedMode = wasLinearized;
            expandOSSNodes = wasExpandOss;
            setHideIntermediateSteps(wasIntermediate);
            setHideAutomodeSteps(wasAutomode);
            setHideClosedSubtrees(wasClosed);
            setHideInteractiveGoals(wasInteractive);
            refresh();
            if (tree.getRoot() != null) {
                collapseEntireTree();
                applyExpandedBranches(tree.getRoot(), originallyExpanded);
                revealSelectedNode();
            }
        }
        if (!problems.isEmpty()) {
            return "FAIL: " + String.join("; ", problems);
        }
        return "PASS: linearized, OSS rows, whole-tree actions, filter counting, view states";
    }

    /**
     * P3b/B12: headless self test of the proof-tree "Strategy Macros" submenu (run from the
     * {@code key.fx.verify.prooftree} harness on the FX thread): repopulates the submenu from the
     * current context (the invoked node, or the selection/root fallback of
     * {@link #populateStrategyMacros()}) and asserts the menu is enabled with a loaded proof and
     * that its macro items are EXACTLY the {@code canApplyTo}-applicable registered macros of the
     * current context node (the count seam — Swing ProofMacroMenu.java:87-99; the PROOF_SCRIPTS
     * entries are excluded: they carry no macro semantics and are gated by the feature). On a
     * closed proof (e.g. the demo autoprove run) no macro is applicable and an empty, enabled
     * submenu is the Swing-equivalent state (Swing would not even add it,
     * ProofTreePopupFactory.java:100-102).
     *
     * @return {@code "PASS ..."} or {@code "FAIL ..."}; the item count is included for the log
     */
    public String verifyStrategyMacros() {
        populateStrategyMacros();
        if (strategyMacrosMenu == null) {
            return "SKIP - no macro submenu";
        }
        List<String> labels = new ArrayList<>();
        int separators = 0;
        for (MenuItem item : strategyMacrosMenu.getItems()) {
            if (item instanceof SeparatorMenuItem) {
                separators++;
            } else {
                labels.add(macroMenuItemText(item));
            }
        }
        Node node = popupNode != null ? popupNode
                : mediator != null && mediator.getSelectedNode() != null
                        ? mediator.getSelectedNode()
                        : proof.root();
        List<String> expected = ProofMacroMenuF.applicableMacroNames(proof,
            proof.getSubtreeEnabledGoals(node), null);
        List<String> scripts = List.of("Run proof script from file...", "Input proof script...");
        List<String> macroLabels = labels.stream().filter(l -> !scripts.contains(l)).toList();
        boolean ok = !strategyMacrosMenu.isDisable() && macroLabels.equals(expected);
        String detail = "macro submenu " + macroLabels.size() + " items, " + separators
            + " separators, disabled=" + strategyMacrosMenu.isDisable();
        if (!ok && !macroLabels.equals(expected)) {
            detail += ", actual=" + macroLabels + ", expected=" + expected;
        }
        return (ok ? "PASS" : "FAIL") + " - " + detail;
    }

    /** P3b/B12: the visible text of the macro submenu items (label-backed custom items). */
    private static String macroMenuItemText(MenuItem item) {
        String text = item.getText();
        if (text != null && !text.isEmpty()) {
            return text;
        }
        if (item instanceof CustomMenuItem custom && custom.getContent() instanceof Label label) {
            return label.getText();
        }
        return "";
    }

    /** @return the number of OSS protocol rows currently present in the tree */
    private static long countOssRows(TreeItem<Entry> item) {
        long count = 0;
        if (item.getValue() != null && item.getValue().isOssChild()) {
            count++;
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            count += countOssRows(child);
        }
        return count;
    }

    /** @return the number of expanded OSS node rows (parents of protocol rows) in the tree */
    private static long countExpandedOssParents(TreeItem<Entry> item) {
        long count = 0;
        Entry entry = item.getValue();
        if (entry != null && !entry.isBranch() && !entry.isOssChild()
                && item.isExpanded()
                && entry.node() != null
                && entry.node().getAppliedRuleApp() instanceof OneStepSimplifierRuleApp) {
            count++;
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            count += countExpandedOssParents(child);
        }
        return count;
    }

    /** @return whether only the root item is expanded below the given item */
    private static boolean onlyRootExpanded(TreeItem<Entry> root) {
        if (!root.isExpanded()) {
            return false;
        }
        for (TreeItem<Entry> child : root.getChildren()) {
            if (isAnyExpanded(child)) {
                return false;
            }
        }
        return true;
    }

    private static boolean isAnyExpanded(TreeItem<Entry> item) {
        if (item.isExpanded()) {
            return true;
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            if (isAnyExpanded(child)) {
                return true;
            }
        }
        return false;
    }

    /** @return the number of expanded rows below and including {@code item} */
    private static long countExpandedRows(TreeItem<Entry> item) {
        long count = item.isExpanded() ? 1 : 0;
        for (TreeItem<Entry> child : item.getChildren()) {
            count += countExpandedRows(child);
        }
        return count;
    }

    /**
     * C25: whether any displayed node entry sits before a later sibling of its parent — under
     * "hide intermediate proofsteps" without active global filters the Swing counting rule keeps
     * only the last child, so such an entry would violate the rule.
     */
    private static boolean hasNonLastNodeEntry(TreeItem<Entry> item) {
        List<TreeItem<Entry>> children = item.getChildren();
        for (int i = 0; i < children.size() - 1; i++) {
            Entry entry = children.get(i).getValue();
            if (entry != null && !entry.isBranch() && !entry.isOssChild()) {
                return true;
            }
        }
        for (TreeItem<Entry> child : children) {
            if (hasNonLastNodeEntry(child)) {
                return true;
            }
        }
        return false;
    }

    private static TreeItem<Entry> firstBranchItem(TreeItem<Entry> item) {
        // the root item is itself a branch; a meaningful expansion test needs a sub-branch below
        for (TreeItem<Entry> child : item.getChildren()) {
            TreeItem<Entry> found = firstBranchBelow(child);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    private static TreeItem<Entry> firstBranchBelow(TreeItem<Entry> item) {
        if (item.getValue() != null && item.getValue().isBranch()) {
            return item;
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            TreeItem<Entry> found = firstBranchBelow(child);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    private boolean isBranchExpanded(Node branchRoot) {
        TreeItem<Entry> item = findBranchItem(tree.getRoot(), branchRoot);
        return item != null && item.isExpanded();
    }

    private static TreeItem<Entry> findBranchItem(TreeItem<Entry> item, Node branchRoot) {
        if (item.getValue() != null && item.getValue().isBranch()
                && item.getValue().node() == branchRoot) {
            return item;
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            TreeItem<Entry> found = findBranchItem(child, branchRoot);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    /** @return the number of entries (node + branch + OSS rows) currently displayed */
    private int countEntries() {
        int[] counters = { 0, 0, 0 };
        collect(tree.getRoot(), Collections.newSetFromMap(new IdentityHashMap<>()), counters);
        return counters[0] + counters[1] + counters[2];
    }

    /**
     * Collects the entries of the collapsed tree: matching node entries, non-matching node
     * entries and branch folders are counted separately.
     */
    private void checkCollapsed(TreeItem<Entry> item, int[] counters) {
        Entry entry = item.getValue();
        if (entry != null && entry.node != null) {
            if (entry.isBranch()) {
                counters[2]++;
            } else if (matches(entry)) {
                counters[0]++;
            } else {
                counters[1]++;
            }
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            checkCollapsed(child, counters);
        }
    }

    private static void collect(TreeItem<Entry> item, Set<Node> seen, int[] counters) {
        Entry entry = item.getValue();
        if (entry != null && entry.node != null) {
            if (entry.isOssChild()) {
                // P3a (C21): OSS protocol rows are decorative sub-rows of their node entry —
                // the node is already seen via the node row, only the extra row is counted
                counters[2]++;
            } else {
                seen.add(entry.node);
                if (entry.isBranch()) {
                    counters[1]++;
                } else {
                    counters[0]++;
                }
            }
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            collect(child, seen, counters);
        }
    }

    private TreeItem<Entry> buildBranch(Node branchRoot, String label) {
        TreeItem<Entry> branchItem = new TreeItem<>(Entry.branch(branchRoot, label));

        // P3a: collect the branch's linear chain first (Swing GUIBranchNode.fillChildrenCache).
        // The chain walk follows the *visible* children (Swing GUIAbstractTreeNode.findChild):
        // with a global filter active a subtree can be inlined even if the node has several
        // children (C25 — the node-filter "counting rule" keeps such an inlined split visible);
        // in linearized mode (C20) a "main"-tagged taclet split continues the chain with its
        // first child and turns the remaining children into branch folders.
        List<TreeItem<Entry>> childItems = new ArrayList<>();
        List<Node> branchChildren = new ArrayList<>();
        boolean searchActive = filterActive();
        // Swing: while the collapsing search is active it takes precedence over the
        // intermediate-step filters (GUIProofTreeModel.bypassNodeFilter)
        boolean nodeFilterActive =
            !searchActive && (hideIntermediateSteps() || hideAutomodeSteps());

        Node current = branchRoot;
        while (true) {
            if (!searchActive || matches(current)) {
                TreeItem<Entry> stepItem = new TreeItem<>(Entry.node(current));
                childItems.add(stepItem);
                // C21: one-step-simplification protocol children (Swing GUIProofTreeNode
                // .ensureChildrenArray): a row per rule application performed inside the OSS
                // step, only visible when the node row is expanded. While the collapsing search
                // is active the rows are omitted so the collapsed tree shows matching steps only
                // (Swing's search filter operates on step rows, the OSS children are decorative).
                if (!searchActive
                        && current.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp oss) {
                    OneStepSimplifier.Protocol protocol = oss.getProtocol();
                    if (protocol != null) {
                        int formulaNr =
                            current.sequent().formulaNumberInSequent(oss.posInOccurrence());
                        for (RuleApp step : protocol) {
                            stepItem.getChildren().add(new TreeItem<>(Entry.oss(current, step,
                                formulaNr)));
                        }
                    }
                }
            }
            List<Node> nextN = visibleChildren(current);
            if (nextN.isEmpty()) {
                if (current.childrenCount() > 0) {
                    // the chain stopped at a split point (more than one child, no inlining):
                    // each child becomes a branch folder below — Swing
                    // GUIBranchNode.fillChildrenCache iterates model.children() once findChild
                    // returns null; the per-child hidden check in the folder loop prunes the
                    // children hidden by global filters again (an empty visible list with an
                    // active filter means all children are hidden, so the folders vanish too)
                    for (int i = 0; i < current.childrenCount(); i++) {
                        branchChildren.add(current.child(i));
                    }
                }
                break;
            }
            if (nextN.size() > 1) {
                if (linearizedMode && isMainTaggedTacletSplit(current)) {
                    // C20: continue the main branch on the same level; the other children become
                    // branch folders below (Swing GUIBranchNode.fillChildrenCache:85-101)
                    for (int i = 1; i < nextN.size(); i++) {
                        branchChildren.add(nextN.get(i));
                    }
                    current = nextN.get(0);
                    continue;
                }
                branchChildren.addAll(nextN);
                break;
            }
            current = nextN.get(0);
        }

        // at a branch point (or a leaf): one branch item per visible child, pruned by the global
        // filters (Swing fillChildrenCache's final loop). Read by index instead of iterating the
        // live children list: the prover thread may add children concurrently.
        for (Node child : branchChildren) {
            if (hiddenByGlobalFilters(child)) {
                // the search filter is part of hiddenByGlobalFilters (containsMatch)
                continue;
            }
            childItems.add(buildBranch(child, ensureBranchLabelIsSet(child)));
        }

        // C25: the node filters (hide intermediate / hide non-interactive) count over the child
        // list like the Swing NodeFilter (ProofTreeViewFilter.countChild) — including the
        // "inlined because of a hidden subtree" rule
        if (nodeFilterActive) {
            List<TreeItem<Entry>> filtered = new ArrayList<>();
            for (int i = 0; i < childItems.size(); i++) {
                TreeItem<Entry> item = childItems.get(i);
                Entry entry = item.getValue();
                // branch folders and OSS protocol rows are always counted (Swing
                // ProofTreeViewFilter.countChild keeps GUIBranchNode children)
                if (entry.isBranch() || entry.isOssChild()) {
                    filtered.add(item);
                } else if (countChainStep(entry.node(), childItems, i)) {
                    filtered.add(item);
                }
            }
            childItems = filtered;
        }
        branchItem.getChildren().setAll(childItems);
        return branchItem;
    }

    /**
     * @param node a proof node
     * @return the node's children that survive the global filters, mirroring Swing
     *         {@code GUIAbstractTreeNode.findChild} (GUIAbstractTreeNode.java:139-167): a single
     *         child always continues the chain; with an active global filter or in linearized
     *         mode the multi-child case keeps the visible children, otherwise the chain stops.
     */
    private List<Node> visibleChildren(Node node) {
        if (node.childrenCount() == 1) {
            return List.of(node.child(0));
        }
        if (!globalFilterActive() && !linearizedMode) {
            return List.of();
        }
        List<Node> visible = new ArrayList<>();
        for (int i = 0; i < node.childrenCount(); i++) {
            Node child = node.child(i);
            if (!hiddenByGlobalFilters(child)) {
                visible.add(child);
            }
        }
        return visible;
    }

    /**
     * @return whether any global filter is active (the collapsing search, Hide Closed Subtrees
     *         or Hide Subtrees Whose Goals are Interactive) — Swing
     *         {@code ProofTreeViewFilter.anyGlobalFilterActive}
     */
    private boolean globalFilterActive() {
        return filterActive() || hideClosedSubtrees() || hideInteractiveGoals();
    }

    /**
     * C20: whether the node's applied rule is a taclet whose <em>last</em> goal template is
     * tagged {@code "main"} — such a split continues in linearized mode (Swing
     * {@code GUIBranchNode.fillChildrenCache:83-88}).
     */
    private static boolean isMainTaggedTacletSplit(Node node) {
        RuleApp app = node.getAppliedRuleApp();
        if (!(app != null && app.rule() instanceof Taclet taclet)) {
            return false;
        }
        ImmutableList<TacletGoalTemplate> templates = taclet.goalTemplates();
        return templates.size() > 0 && "main".equals(templates.last().tag());
    }

    /**
     * C25: whether the chain step at {@code pos} in {@code siblings} is counted by the active
     * node filter (Swing {@code HideIntermediateFilter}/{@code OnlyInteractiveFilter}
     * {@code countChild}, ProofTreeViewFilter.java:214-282): the last child is always shown;
     * with a global filter active, a split that was inlined because its sibling subtree is
     * hidden is shown too.
     */
    private boolean countChainStep(Node node, List<TreeItem<Entry>> siblings, int pos) {
        if (!hideIntermediateSteps() && node.getNodeInfo().getInteractiveRuleApplication()) {
            // Hide Non-interactive Proofsteps keeps interactive steps
            return true;
        }
        if (pos == siblings.size() - 1) {
            return true;
        }
        if (globalFilterActive() && !siblings.get(pos + 1).getValue().isBranch()
                && node.childrenCount() != 1) {
            return true;
        }
        return false;
    }

    /**
     * @return whether the subtree starting at {@code node} is hidden by an active global filter
     *         (Swing {@code ProofTreeViewFilter.hiddenByGlobalFilters}): the search filter, Hide
     *         Closed Subtrees and Hide Subtrees Whose Goals are Interactive
     */
    private boolean hiddenByGlobalFilters(Node node) {
        if (filterActive() && !containsMatch(node)) {
            return true;
        }
        if (hideClosedSubtrees() && node.isClosed()) {
            return true;
        }
        if (hideInteractiveGoals() && subtreeGoalsAllInteractive(node)) {
            return true;
        }
        return false;
    }

    /**
     * @return whether the subtree rooted at {@code node} has open goals but none of them is
     *         automatic (Swing {@code HideInteractiveGoalsFilter.showSubtree} hides such
     *         subtrees; subtrees without goals stay visible)
     */
    private boolean subtreeGoalsAllInteractive(Node node) {
        ImmutableList<Goal> goals = proof.getSubtreeGoals(node);
        if (goals.isEmpty()) {
            return false;
        }
        for (Goal goal : goals) {
            if (goal.isAutomatic()) {
                return false;
            }
        }
        return true;
    }

    // -----------------------------------------------------------------------
    // Filters (Swing ProofTreeViewFilter, state in ProofIndependentSettings)
    // -----------------------------------------------------------------------

    private static boolean hideIntermediateSteps() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .getHideIntermediateProofsteps();
    }

    private static boolean hideAutomodeSteps() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .getHideAutomodeProofsteps();
    }

    private static boolean hideClosedSubtrees() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getHideClosedSubtrees();
    }

    private static boolean hideInteractiveGoals() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .getHideInteractiveGoals();
    }

    private static void setHideIntermediateSteps(boolean active) {
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .setHideIntermediateProofsteps(active);
    }

    private static void setHideAutomodeSteps(boolean active) {
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .setHideAutomodeProofsteps(active);
    }

    private static void setHideClosedSubtrees(boolean active) {
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHideClosedSubtrees(active);
    }

    private static void setHideInteractiveGoals(boolean active) {
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHideInteractiveGoals(active);
    }

    /**
     * Builds the right-click context menu: the four view filters and the tree controls (C20
     * linearized mode, C21 OSS expansion, C22 whole-tree expand/collapse) — the FX docking
     * framework has no tab-title "Settings" gear menu like the Swing dockable, so these live
     * here — plus the popup actions of the Swing {@code ProofTreePopupFactory}: Apply Strategy,
     * Prune, Edit Notes, the per-node expand/collapse and sibling actions, the goals enablement
     * and P3a's Show Subtree Statistics, and finally (P4, C24) the PROOF_TREE extension
     * contributions after a separator (Swing ProofTreePopupFactory.java:152-154). Delayed Cut
     * (feature-flagged) and the macro submenu (B12, P3b) are not yet ported.
     */
    private ContextMenu createContextMenu() {
        // reviewer request: the filter toggles are built from the registered filters
        // (addFilter), not hard-coded — the two node filters exclude each other (Swing keeps
        // only one node filter active)
        List<CheckMenuItem> filterItems = new ArrayList<>(filters.size());
        for (ProofTreeFilterF filter : filters) {
            CheckMenuItem item = new CheckMenuItem(filter.name());
            item.setSelected(filter.isActive());
            item.setOnAction(e -> {
                filter.setActive(item.isSelected());
                if (item.isSelected()) {
                    for (int j = 0; j < filters.size(); j++) {
                        if (filters.get(j) != filter && filter.isExclusiveWith(filters.get(j))
                                && filters.get(j).isActive()) {
                            filters.get(j).setActive(false);
                            filterItems.get(j).setSelected(false);
                        }
                    }
                }
                refresh();
            });
            filterItems.add(item);
        }
        CheckMenuItem hideIntermediateItem = filterItems.get(0);
        CheckMenuItem onlyInteractiveItem = filterItems.get(1);
        CheckMenuItem hideClosedItem = filterItems.get(2);
        CheckMenuItem hideInteractiveItem = filterItems.get(3);
        // C20/C21 (P3a): the linearized mode and the OSS expansion toggles (Swing
        // ProofTreeSettingsMenuFactory creates both as checkboxes of the "Settings" gear menu)
        CheckMenuItem linearizeItem = new CheckMenuItem("Linearize Proof Tree");
        linearizeItem.setSelected(linearizedMode);
        linearizeItem.setOnAction(e -> {
            boolean isChange = linearizedMode != linearizeItem.isSelected();
            linearizedMode = linearizeItem.isSelected();
            if (isChange) {
                refresh();
            }
        });
        CheckMenuItem expandOssItem = new CheckMenuItem("Expand One Step Simplifications nodes");
        expandOssItem.setSelected(expandOSSNodes);
        expandOssItem.setOnAction(e -> expandOSSNodes = expandOssItem.isSelected());
        // C22 (P3a): whole-tree actions (Swing ProofTreeSettingsMenuFactory createExpandAll /
        // createCollapseAll, operating on the whole tree instead of one subtree)
        MenuItem expandAllItem = actionItem("Expand All", IconFactoryF.Key.PLUS,
            this::expandEntireTree);
        MenuItem collapseAllItem = actionItem("Collapse All", IconFactoryF.Key.MINUS,
            this::collapseEntireTree);
        // C23 (P3a): the Swing popup's prover-control actions (ProofTreePopupFactory
        // RunStrategyOnNode / Prune / Notes)
        MenuItem applyStrategyItem = actionItem("Apply Strategy", IconFactoryF.Key.START,
            this::runStrategyOnNode);
        MenuItem pruneItem = actionItem("Prune Proof", IconFactoryF.Key.PRUNE,
            this::prunePopupNode);
        // P3b/B12: the "Strategy Macros" submenu right after Prune (Swing
        // ProofTreePopupFactory.initMacroMenu, ProofTreePopupFactory.java:98-103). The items are
        // (re)populated per popup-open from the invoked node, see populateStrategyMacros().
        strategyMacrosMenu = new Menu("Strategy Macros");
        MenuItem notesItem = actionItem("Edit Notes...", null, this::editNotes);
        MenuItem subtreeStatsItem = actionItem("Show Subtree Statistics",
            IconFactoryF.Key.STATISTICS, this::showSubtreeStatistics);
        // D34 (P3c): Swing ProofTreePopupFactory adds OpenCurrentNodeAction as the final popup
        // entry (ProofTreePopupFactory.java:143) — opens the node's sequent in a separate buffer
        MenuItem openNodeItem = actionItem("Open Node in Separate Buffer", null, () -> {
            if (openNodeInSeparateBuffer != null && popupNode != null) {
                openNodeInSeparateBuffer.accept(popupNode);
            }
        });
        ContextMenu menu = new ContextMenu(hideIntermediateItem, onlyInteractiveItem,
            new SeparatorMenuItem(), hideClosedItem, hideInteractiveItem, linearizeItem,
            expandOssItem, new SeparatorMenuItem(), expandAllItem, collapseAllItem,
            new SeparatorMenuItem(), applyStrategyItem, pruneItem, strategyMacrosMenu,
            new SeparatorMenuItem(), notesItem,
            new SeparatorMenuItem(),
            actionItem("Expand All Below", IconFactoryF.Key.PLUS,
                () -> expandAllBelow(popupBranchItem)),
            actionItem("Expand Goals Only Below", IconFactoryF.Key.EXPAND_GOALS,
                () -> expandGoalsOnlyBelow(popupBranchItem)),
            actionItem("Collapse Below", IconFactoryF.Key.MINUS,
                () -> collapseAllBelow(popupBranchItem)),
            actionItem("Collapse Other Branches", null, () -> collapseOthers(popupBranchItem)),
            new SeparatorMenuItem(),
            actionItem("Previous Sibling", IconFactoryF.Key.PREVIOUS, () -> gotoSibling(-1)),
            actionItem("Next Sibling", IconFactoryF.Key.NEXT, () -> gotoSibling(1)),
            new SeparatorMenuItem(),
            actionItem("Set All Goals Below to Interactive", null, () -> setGoalsBelow(false)),
            actionItem("Set All Goals Below to Automatic", null, () -> setGoalsBelow(true)),
            new SeparatorMenuItem(), subtreeStatsItem, openNodeItem);
        menu.setOnShowing(e -> {
            // pick up changes made elsewhere (e.g. by the classic UI sharing the settings)
            for (int i = 0; i < filters.size(); i++) {
                filterItems.get(i).setSelected(filters.get(i).isActive());
            }
            linearizeItem.setSelected(linearizedMode);
            expandOssItem.setSelected(expandOSSNodes);
            // C23: enablement mirrors the Swing popup — Apply Strategy needs a proof, Prune only
            // makes sense on an inner node whose subtree still has something to prune, Notes and
            // the statistics need a proof
            applyStrategyItem.setDisable(proof == null);
            notesItem.setDisable(proof == null);
            subtreeStatsItem.setDisable(proof == null);
            pruneItem.setDisable(!isPrunable(popupNode));
            // P3b/B12: rebuild the macro submenu from the invoked node (Swing
            // ProofTreePopupFactory.initMacroMenu rebuilds it per popup-open)
            populateStrategyMacros();
            // D34: Opening a node buffer needs a proof node to open
            openNodeItem.setDisable(proof == null || popupNode == null);
            refreshPopupExtensions();
        });
        // P3b/B12: the submenu is persistent (unlike the term menu / sequent popup, which are
        // rebuilt per show and pick up the PROOF_SCRIPTS feature at build time), so it gets the
        // live feature listener of the Swing ProofMacroMenu (ProofMacroMenu.java:125-133). The
        // listener immediately re-populates with the current value; on the FX thread, since it
        // touches the menu items (the feature may be toggled from the settings dialog's thread).
        FeatureSettings.onAndActivate(ProofMacroMenuF.PROOF_SCRIPTS_FEATURE,
            active -> FxUtil.runLater(this::populateStrategyMacros));
        return menu;
    }

    /**
     * P3b/B12: (re)populates the persistent "Strategy Macros" submenu for the currently invoked
     * node ({@link #popupNode}; falls back to the mediator's selected node and then to the proof
     * root for the headless self test): the applicable macros of the registered-macro superset
     * ({@link ProofMacroMenuF}), category-grouped, plus the PROOF_SCRIPTS section according to
     * the current feature state — the exact content of the Swing {@code ProofMacroMenu}.
     * <p>
     * The macro items run on the {@link #popupNode} of the invocation (Swing's
     * {@code ProofMacroUserAction} runs them on the mediator selection — a quirk of reusing the
     * same action factory for the tree popup; the invoked node is the deliberate FX choice).
     * Without a proof the submenu is disabled and empty (Swing's
     * {@code mediator.enableWhenProofLoaded(this)}).
     */
    private void populateStrategyMacros() {
        if (strategyMacrosMenu == null) {
            return;
        }
        strategyMacrosMenu.getItems().clear();
        if (proof == null || proof.isDisposed() || proofControl == null) {
            strategyMacrosMenu.setDisable(true);
            return;
        }
        Node node = popupNode != null ? popupNode
                : mediator != null && mediator.getSelectedNode() != null
                        ? mediator.getSelectedNode()
                        : proof.root();
        strategyMacrosMenu.setDisable(false);
        strategyMacrosMenu.getItems().addAll(ProofMacroMenuF.items(proof,
            proof.getSubtreeEnabledGoals(node), node, proofControl, null));
    }

    /**
     * C24 (P4): the PROOF_TREE extension contributions spliced at the end of the popup — the
     * items of {@code KeYGuiExtensionFacadeF.getProofTreeContextItems} for the clicked node
     * behind a separator (Swing {@code ProofTreePopupFactory.create},
     * ProofTreePopupFactory.java:152-154: {@code menu.addSeparator(); addContextMenuItems(
     * ContextMenuKind.PROOF_TREE, menu, context.invokedNode, context.mediator);} followed by
     * dropping the separator when nothing was contributed). Rebuilt on every showing since the
     * clicked node changes; the section always stays the tail of the menu.
     */
    private void refreshPopupExtensions() {
        contextMenu.getItems().removeAll(popupExtensionItems);
        popupExtensionItems.clear();
        if (mediator == null) {
            return;
        }
        List<MenuItem> items =
            KeYGuiExtensionFacadeF.getProofTreeContextItems(mediator, popupNode);
        if (items.isEmpty()) {
            return; // no separator without contributions (Swing drops it too)
        }
        popupExtensionItems.add(new SeparatorMenuItem());
        popupExtensionItems.addAll(items);
        contextMenu.getItems().addAll(popupExtensionItems);
    }

    /** @return a menu item with an optional icon and the given action */
    private static MenuItem actionItem(String label, IconFactoryF.Key icon, Runnable action) {
        MenuItem item = new MenuItem(label);
        if (icon != null) {
            item.setGraphic(IconFactoryF.createIcon(icon));
        }
        item.setOnAction(e -> action.run());
        return item;
    }

    // -----------------------------------------------------------------------
    // Popup expand/collapse and sibling actions (Swing ProofTreePopupFactory)
    // -----------------------------------------------------------------------

    /**
     * C22 (P3a): expands the whole tree (Swing {@code ProofTreeSettingsMenuFactory}
     * {@code CreateExpandAll} / {@code ProofTreeExpansionState.expandAll}): everything except
     * the one-step-simplification nodes unless {@link #expandOSSNodes} is set — their protocol
     * rows stay collapsed like in Swing's default ({@code ProofTreePopupFactory.ossPathFilter}).
     */
    void expandEntireTree() {
        TreeItem<Entry> root = tree.getRoot();
        if (root == null) {
            return;
        }
        root.setExpanded(true);
        expandRec(root);
    }

    /**
     * C22 (P3a): collapses the whole tree below the root (Swing
     * {@code ProofTreeSettingsMenuFactory.createCollapseAll}; the root row is re-expanded).
     */
    void collapseEntireTree() {
        TreeItem<Entry> root = tree.getRoot();
        if (root == null) {
            return;
        }
        for (TreeItem<Entry> child : new ArrayList<>(root.getChildren())) {
            collapseRec(child);
        }
        root.setExpanded(true);
    }

    /** Expands every branch below the given item (Swing Expand All Below). */
    private void expandAllBelow(TreeItem<Entry> item) {
        if (item == null) {
            return;
        }
        expandRec(item);
    }

    /**
     * Recursively expands the item and its children; an OSS node row (a proof node whose applied
     * rule is the one-step simplifier) and its protocol rows are only expanded when
     * {@link #expandOSSNodes} is set (Swing {@code ProofTreeExpansionState.expandAll} with the
     * OSS path filter {@code ProofTreePopupFactory.ossPathFilter}).
     */
    private void expandRec(TreeItem<Entry> item) {
        if (item.getValue() != null && item.getValue().isOssChild()) {
            return;
        }
        if (item.getValue() != null && !item.getValue().isBranch()
                && item.getValue().node() != null
                && item.getValue().node().getAppliedRuleApp() instanceof OneStepSimplifierRuleApp
                && !expandOSSNodes) {
            return; // OSS protocol rows stay collapsed unless "Expand OSS nodes" is set
        }
        item.setExpanded(true);
        for (TreeItem<Entry> child : new ArrayList<>(item.getChildren())) {
            expandRec(child);
        }
    }

    /** Collapses every branch below the given item, the item itself stays expanded. */
    private void collapseAllBelow(TreeItem<Entry> item) {
        if (item == null) {
            return;
        }
        for (TreeItem<Entry> child : new ArrayList<>(item.getChildren())) {
            collapseRec(child);
        }
    }

    private static void collapseRec(TreeItem<Entry> item) {
        item.setExpanded(false);
        for (TreeItem<Entry> child : new ArrayList<>(item.getChildren())) {
            collapseRec(child);
        }
    }

    /**
     * Collapses everything below the given branch and then expands the branches along the paths
     * of the open goals, so only the goals remain visible (Swing Expand Goals Only Below).
     */
    private void expandGoalsOnlyBelow(TreeItem<Entry> branchItem) {
        if (branchItem == null) {
            return;
        }
        collapseAllBelow(branchItem);
        branchItem.setExpanded(true);
        for (Goal goal : proof.openGoals()) {
            TreeItem<Entry> item = findItem(branchItem, goal.node());
            for (TreeItem<Entry> i = item == null ? null : item.getParent(); i != null
                    && i != branchItem.getParent(); i = i.getParent()) {
                i.setExpanded(true);
            }
        }
    }

    /**
     * Collapses every expanded branch that is neither the given branch nor one of its ancestors
     * (Swing {@code collapseOthers}).
     */
    private void collapseOthers(TreeItem<Entry> target) {
        if (target == null) {
            return;
        }
        collapseOthersRec(tree.getRoot(), target);
    }

    private static void collapseOthersRec(TreeItem<Entry> item, TreeItem<Entry> target) {
        if (item == null || !item.isExpanded() || item == target) {
            return;
        }
        if (isAncestorOf(item, target)) {
            for (TreeItem<Entry> child : new ArrayList<>(item.getChildren())) {
                collapseOthersRec(child, target);
            }
        } else {
            item.setExpanded(false);
        }
    }

    private static boolean isAncestorOf(TreeItem<?> ancestor, TreeItem<?> item) {
        for (TreeItem<?> i = item; i != null; i = i.getParent()) {
            if (i == ancestor) {
                return true;
            }
        }
        return false;
    }

    /**
     * Selects the next ({@code direction == 1}) or previous ({@code direction == -1}) branch
     * sibling of the selected entry's branch (Swing Previous/Next Sibling): the immediate
     * neighbor first, then wrapping around from the far end like the Swing actions.
     */
    private void gotoSibling(int direction) {
        TreeItem<Entry> start = tree.getSelectionModel().getSelectedItem();
        if (start == null) {
            return;
        }
        TreeItem<Entry> branchItem = start.getValue().isBranch() ? start : start.getParent();
        if (branchItem == null || !branchItem.getValue().isBranch()) {
            return;
        }
        TreeItem<Entry> parent = branchItem.getParent();
        if (parent == null) {
            return;
        }
        List<TreeItem<Entry>> children = new ArrayList<>(parent.getChildren());
        int index = children.indexOf(branchItem);
        int count = children.size();
        if (index < 0 || count < 2) {
            return;
        }
        List<Integer> candidates = new ArrayList<>();
        candidates.add(index + direction);
        if (direction < 0) {
            for (int i = count - 1; i > index; i--) {
                candidates.add(i);
            }
        } else {
            for (int i = 0; i < index; i++) {
                candidates.add(i);
            }
        }
        for (int candidate : candidates) {
            if (candidate < 0 || candidate >= count) {
                continue;
            }
            TreeItem<Entry> sibling = children.get(candidate);
            if (sibling.getValue().isBranch()) {
                tree.getSelectionModel().select(sibling);
                tree.scrollTo(tree.getRow(sibling));
                return;
            }
        }
    }

    /**
     * Sets the automatic state of all open goals below the node the popup was invoked on (Swing
     * {@code SetGoalsBelowEnableStatus}, {@code Proof.getSubtreeGoals}). The goal list picks the
     * change up via its goal listener; the tree is refreshed because the "hide interactive
     * goals" filter depends on the goal states.
     */
    private void setGoalsBelow(boolean enable) {
        if (proof == null || proof.isDisposed() || popupNode == null) {
            return;
        }
        for (Goal goal : proof.getSubtreeGoals(popupNode)) {
            goal.setEnabled(enable);
        }
        refresh();
    }

    // -----------------------------------------------------------------------
    // P3a (C23): popup prover-control actions (Swing ProofTreePopupFactory)
    // -----------------------------------------------------------------------

    /**
     * Gives the tree the mediator + proof control of the loaded environment (Swing
     * {@code ProofTreeView} extracts both from the mediator): the Apply Strategy and Prune
     * popup actions and the auto-mode partial updates ({@link #autoModeStarted}
     * /{@link #autoModeStopped}) need them.
     */
    public void setActionContext(KeYMediatorF mediator, ProofControl proofControl) {
        Objects.requireNonNull(mediator);
        this.mediator = mediator;
        if (this.proofControl != null) {
            this.proofControl.removeAutoModeListener(this);
        }
        this.proofControl = proofControl;
        if (proofControl != null) {
            proofControl.addAutoModeListener(this);
        }
    }

    /**
     * D34 (P3c): installs the "Open Node in Separate Buffer" popup handler (Swing
     * {@code SequentViewDock.OpenCurrentNodeAction}); the consumer opens a
     * {@link de.uka.ilkd.key.gui.fx.docking.SequentViewDockF} for the given node.
     *
     * @param openNode the consumer handling the popup action, or {@code null} to uninstall
     */
    public void setOpenNodeInSeparateBuffer(Consumer<Node> openNode) {
        this.openNodeInSeparateBuffer = openNode;
    }

    /**
     * C23: runs the automatic strategy on the subtree of the node the popup was invoked on
     * (Swing {@code RunStrategyOnNodeUserAction}): all enabled goals below the node, or the node
     * itself when it is an open goal.
     */
    private void runStrategyOnNode() {
        if (proof == null || proof.isDisposed() || popupNode == null || mediator == null
                || proofControl == null) {
            return;
        }
        Goal invokedGoal = proof.getOpenGoal(popupNode);
        ImmutableList<Goal> goals = invokedGoal != null
                ? ImmutableList.of(invokedGoal)
                : proof.getSubtreeEnabledGoals(popupNode);
        mediator.startAutoMode(goals);
    }

    /**
     * C23: prunes the proof below the node the popup was invoked on (Swing {@code Prune} calls
     * {@code KeYMediator.setBack(context.invokedNode)}).
     */
    private void prunePopupNode() {
        if (mediator == null || popupNode == null) {
            return;
        }
        mediator.pruneNode(popupNode);
    }

    /**
     * C23 (WP-10): headless self test of the tree popup's "Apply Strategy" and "Prune Proof"
     * actions. The popup is prepared on the clicked item through the same {@link #preparePopup}
     * seam the context-request handler drives (with the tree selection parked elsewhere first,
     * so the clicked node — not the previous selection — becomes the popup node), then the real
     * "Apply Strategy" action handler runs.
     * <p>
     * Must be called on the FX thread (from the {@code key.fx.verify.prooftree} harness's
     * {@code runOnFx} block, like {@link #verifyStrategyMacros()}); the strategy runs
     * asynchronously like in the real UI, the harness continues with
     * {@link #verifyApplyStrategyAtNodeResult()} on its worker thread. Skipped (reported, not
     * failed) without a proof / proof control / mediator, while a run is active, or when no
     * enabled goal exists below the clicked node (e.g. a closed demo proof after a full auto
     * mode).
     *
     * @return {@code "PASS..."} / {@code "FAIL - ..."} / {@code "SKIP - ..."} for the harness
     */
    public String verifyApplyStrategyAtNode() {
        if (proof == null || proof.isDisposed() || mediator == null || proofControl == null) {
            return "SKIP - no proof/mediator/proof control";
        }
        if (mediator.autoModeRunningProperty().get()) {
            return "SKIP - auto mode running";
        }
        // the clicked node: the proof root (its subtree holds the enabled goals); the selection
        // is parked on a different item when one exists, so the "acts on the clicked node" seam
        // is exercised with selection != clicked node
        Node clicked = proof.root();
        if (proof.getSubtreeEnabledGoals(clicked).isEmpty()) {
            return "SKIP - no enabled goals below the clicked node";
        }
        TreeItem<Entry> clickedItem = findItem(tree.getRoot(), clicked);
        if (clickedItem == null) {
            return "SKIP - the clicked node has no tree item";
        }
        applyStrategyNodesBefore = countNodesBelow(clicked);
        TreeItem<Entry> parkItem = findOtherItem(tree.getRoot(), clickedItem);
        if (parkItem != null) {
            tree.getSelectionModel().select(parkItem);
        }
        boolean parked = tree.getSelectionModel().getSelectedItem() != clickedItem;
        // the popup preparation seam: the invoked node must be the clicked node (Swing
        // setSelectionPath(selPath) + ProofTreeContext from selPath), not the parked selection,
        // and the selection follows the click like in Swing
        preparePopup(clickedItem);
        boolean popupNodeOk = popupNode == clicked
                && tree.getSelectionModel().getSelectedItem() == clickedItem;
        // cap the step budget for the self test's strategy run (open goals must remain below
        // the clicked node for the prune part; restored by verifyApplyStrategyAtNodeResult)
        applyStrategySavedMaxSteps = proof.getSettings().getStrategySettings().getMaxSteps();
        proof.getSettings().getStrategySettings().setMaxSteps(APPLY_STRATEGY_MAX_STEPS);
        if (popupNodeOk) {
            // the real popup action: runs the strategy on the goals of the clicked node
            runStrategyOnNode();
        }
        return (popupNodeOk ? "PASS" : "FAIL") + " - popup on clicked node, nodes before="
            + applyStrategyNodesBefore + ", parkedSelection=" + parked;
    }

    /**
     * Worker-thread continuation of {@link #verifyApplyStrategyAtNode()}: waits for the strategy
     * run to change the proof below the clicked node, then runs the real "Prune Proof" popup
     * action on the first child of the clicked node and asserts its subtree was removed (Swing
     * {@code KeYMediator.setBack} → {@code Proof.pruneProof}).
     *
     * @return the PASS/FAIL detail for the harness report
     */
    public String verifyApplyStrategyAtNodeResult() {
        if (proof == null || proof.isDisposed()) {
            return "SKIP - no proof";
        }
        try {
            return doVerifyApplyStrategyAtNodeResult();
        } finally {
            // restore the demo proof's step budget (capped for the self test's strategy run)
            proof.getSettings().getStrategySettings().setMaxSteps(applyStrategySavedMaxSteps);
        }
    }

    private String doVerifyApplyStrategyAtNodeResult() {
        // wait until the strategy run applied rule applications below the clicked node (and
        // stopped, max ~30 s — a no-op start fails the check on the timeout)
        long deadline = System.currentTimeMillis() + 30_000;
        while (System.currentTimeMillis() < deadline
                && (mediator.autoModeRunningProperty().get()
                        || countNodesBelow(proof.root()) <= applyStrategyNodesBefore)) {
            try {
                Thread.sleep(50);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return "FAIL - interrupted while waiting for the strategy run";
            }
        }
        long after = countNodesBelow(proof.root());
        if (after <= applyStrategyNodesBefore) {
            return "FAIL - no rule applications below the clicked node ("
                + applyStrategyNodesBefore + ")";
        }
        // the real prune action on an inner node below the clicked node: the capped strategy
        // run leaves open goals, so the pruning conditions of Proof.pruneProof hold; lift
        // noPruningClosed anyway in case the branch was closed by the (short) run
        Node pruneTarget = proof.root().childrenCount() > 0 ? proof.root().child(0) : null;
        if (pruneTarget == null) {
            return "FAIL - no inner node to prune after the strategy run";
        }
        long prunable = countNodesBelow(pruneTarget);
        boolean noPruningClosedSaved = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        try {
            Boolean prunedOk = FxUtil.callAndWait(() -> {
                TreeItem<Entry> pruneItem = findItem(tree.getRoot(), pruneTarget);
                if (pruneItem == null) {
                    return false;
                }
                preparePopup(pruneItem);
                prunePopupNode();
                return true;
            });
            long afterPrune = countNodesBelow(pruneTarget);
            boolean pruned = prunedOk == Boolean.TRUE && afterPrune == 1;
            return (pruned ? "PASS" : "FAIL") + " - applyStrategy nodes "
                + applyStrategyNodesBefore + "->" + after + ", prune " + prunable + "->"
                + afterPrune + (pruned ? "" : " (prune left " + afterPrune + " nodes)");
        } finally {
            GeneralSettings.noPruningClosed = noPruningClosedSaved;
        }
    }

    /** @return the number of nodes in the subtree of the given node (the node itself included) */
    private long countNodesBelow(Node node) {
        long count = 1;
        for (int i = 0; i < node.childrenCount(); i++) {
            count += countNodesBelow(node.child(i));
        }
        return count;
    }

    /**
     * @return the first tree item of the subtree rooted at {@code start} whose node differs from
     *         {@code exclude}'s node, or {@code null} (the item to park the selection on)
     */
    private static TreeItem<Entry> findOtherItem(TreeItem<Entry> start, TreeItem<Entry> exclude) {
        if (start.getValue() != null && start != exclude) {
            return start;
        }
        for (TreeItem<Entry> child : start.getChildren()) {
            TreeItem<Entry> result = findOtherItem(child, exclude);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    /**
     * C23: whether the Swing {@code Prune} popup item is enabled for the popup node
     * (ProofTreePopupFactory.java:377-398): pruning is disabled for goals and for closed
     * subtrees when the command line flag {@code --no-pruning-closed} is set, enabled when the
     * subtree still contains prunable goals or the node is a cached cutting point.
     */
    private boolean isPrunable(Node node) {
        if (node == null || node.proof() == null
                || node.proof().isOpenGoal(node) || node.proof().isClosedGoal(node)) {
            return false;
        }
        if (node.proof().getSubtreeGoals(node).size() > 0
                || (!GeneralSettings.noPruningClosed
                        && node.proof().getClosedSubtreeGoals(node).size() > 0)
                || node.lookup(ClosedBy.class) != null) {
            return true;
        }
        return false;
    }

    /**
     * C23: opens the proof node notes editor (Swing {@code Notes} popup item): the text is
     * stored on the node via {@code NodeInfo.setNotes} ({@code null} clears it).
     */
    private void editNotes() {
        if (proof == null || proof.isDisposed() || popupNode == null) {
            return;
        }
        String original = popupNode.getNodeInfo().getNotes();
        ProofTreeNotesDialogF dialog = new ProofTreeNotesDialogF(original, popupNode);
        dialog.showNonBlocking();
    }

    /**
     * C23: opens the subtree statistics report for the node the popup was invoked on (Swing
     * {@code ShowProofStatistics}, simplified — the Swing HTML-styled report window with
     * CSV export is ported as a plain-text report; the export follow-up is A4 (P3c)).
     */
    private void showSubtreeStatistics() {
        if (proof == null || proof.isDisposed() || popupNode == null) {
            return;
        }
        SubtreeStatisticsDialogF dialog = new SubtreeStatisticsDialogF(popupNode);
        dialog.showNonBlocking();
    }

    // -----------------------------------------------------------------------
    // P3a (C27): auto-mode partial subtree updates (Swing ProofTreeView
    // autoModeStarted / autoModeStopped, ProofTreeView.java:1072-1137)
    // -----------------------------------------------------------------------

    @Override
    public void autoModeStarted(ProofEvent e) {
        if (e.getSource() != proof) {
            // Auto mode on a proof this view does not display (e.g. an auxiliary side proof of
            // the information-flow macros, see KeY issue #3713): ignore.
            return;
        }
        // save the goals on which the prover may work
        modifiedSubtrees = e.getSource().openGoals().map(Goal::node);
    }

    @Override
    public void autoModeStopped(ProofEvent e) {
        if (proof == null || proof.isDisposed()) {
            modifiedSubtrees = null;
            return;
        }
        final List<Node> changed;
        if (modifiedSubtrees != null) {
            changed = new ArrayList<>();
            for (Node n : modifiedSubtrees) {
                // skip nodes of other proofs; changed = no longer an open goal
                if (n.proof() == proof && proof.openGoals().filter(g -> g.node() == n).isEmpty()) {
                    changed.add(n);
                }
            }
        } else {
            changed = List.of();
        }
        // all tree mutation must happen on the FX thread (Swing marshals via the EDT)
        FxUtil.runLater(() -> {
            modifiedSubtrees = null;
            if (proof == null || proof.isDisposed() || tree.getRoot() == null) {
                return;
            }
            if (changed.size() > MAX_PARTIAL_TREE_UPDATES) {
                // update the whole tree
                fullUpdateAfterAutoCount.incrementAndGet();
                refresh();
            } else if (!changed.isEmpty()) {
                // update only the affected subtrees (Swing delegateModel.updateTree(n));
                // counted at the stop decision so the post-run verification reports it even if
                // the FX work is still queued
                partialUpdateCount.incrementAndGet();
                for (Node n : changed) {
                    partialUpdateSubtree(n);
                }
            }
            revealSelectedNode();
        });
    }

    /**
     * C27: rebuilds the subtree below the nearest branch item of {@code node} in place, keeping
     * the expansion state of the surrounding branches (Swing {@code GUIProofTreeModel.updateTree
     * (Node)}).
     */
    private void partialUpdateSubtree(Node subtreeRoot) {
        FxUtil.runLater(() -> {
            if (proof == null || proof.isDisposed() || tree.getRoot() == null) {
                return;
            }
            TreeItem<Entry> target = nearestBranchItem(tree.getRoot(), subtreeRoot);
            if (target == null) {
                refresh();
                return;
            }
            Set<Node> expanded = Collections.newSetFromMap(new IdentityHashMap<>());
            collectExpandedBranches(target, expanded);
            TreeItem<Entry> rebuilt = buildBranch(target.getValue().node(),
                target.getValue().branchLabel);
            target.getChildren().setAll(new ArrayList<>(rebuilt.getChildren()));
            applyExpandedBranches(target, expanded);
            containsMatchCache.clear();
            updateMatches();
            if (selectionModel != null && selectionModel.getSelectedNode() != null) {
                TreeItem<Entry> sel = findItem(tree.getRoot(), selectionModel.getSelectedNode());
                if (sel != null) {
                    tree.getSelectionModel().select(sel);
                }
            }
        });
    }

    /**
     * @param from the tree item to search (itself a branch)
     * @param node a proof node below the branch
     * @return the deepest branch item whose displayed subtree contains {@code node}, or
     *         {@code null} when the node is not displayed
     */
    private static TreeItem<Entry> nearestBranchItem(TreeItem<Entry> from, Node node) {
        if (from == null || from.getValue() == null || from.getValue().node() == null) {
            return null;
        }
        TreeItem<Entry> result = null;
        for (TreeItem<Entry> child : from.getChildren()) {
            Entry entry = child.getValue();
            if (entry == null || entry.node() == null) {
                continue;
            }
            boolean contains = entry.node() == node || isInSubtree(entry.node(), node);
            if (!contains) {
                continue;
            }
            if (entry.isBranch()) {
                TreeItem<Entry> deeper = nearestBranchItem(child, node);
                result = deeper != null ? deeper : child;
            } else if (result == null) {
                result = from; // the node is on this branch's chain
            }
        }
        return result;
    }

    /** @return whether {@code maybeDescendant} is {@code ancestor} itself or below it */
    private static boolean isInSubtree(Node ancestor, Node maybeDescendant) {
        for (Node n = maybeDescendant; n != null; n = n.parent()) {
            if (n == ancestor) {
                return true;
            }
        }
        return false;
    }

    /**
     * P3a (C27): a one-line report of the auto-mode partial update counters for the
     * verification hook.
     */
    public String getAutoModeReport() {
        return "autoModePartialUpdates=" + partialUpdateCount.get()
            + " autoModeFullUpdates=" + fullUpdateAfterAutoCount.get();
    }

    /**
     * WP-2 (branch editing): whether the given entry is editable like Swing's cell editor
     * {@code isCellEditable} (ProofTreeView.java:243-270): only branch entries whose node has a
     * parent — the root branch ("Proof Tree") is denied.
     */
    private static boolean isEditableBranchEntry(Entry entry) {
        return entry != null && entry.isBranch() && entry.node != null
                && entry.node.parent() != null;
    }

    /**
     * WP-2 (branch editing): applies a branch label edit — the Swing commit path
     * {@code GUIProofTreeModel.valueForPathChanged → GUIBranchNode.setLabel →
     * NodeInfo.setBranchLabel} (GUIProofTreeModel.java:398-405, GUIBranchNode.java:146-154).
     * The tree is rebuilt afterwards (Swing re-renders the model after the edit) so the branch
     * folder picks up the stored label. A {@code null} value is ignored.
     */
    private void commitBranchLabel(Entry entry, String newValue) {
        if (entry == null || !entry.isBranch() || newValue == null) {
            return;
        }
        entry.node.getNodeInfo().setBranchLabel(newValue);
        FxUtil.runLater(this::refresh);
    }

    /**
     * WP-2 verification (branch editing): asserts the Swing {@code isCellEditable} parity (the
     * root branch is denied, a real branch is editable), exercises the F2 path
     * ({@code tree.edit} starts and cancels the cell editor), commits a rename through the
     * {@link #commitBranchLabel} seam, asserts the stored label and the rebuilt entry text, then
     * restores the original label.
     *
     * @return a one-line report, {@code "... PASS"} / {@code "SKIP ..."} when the proof has no
     *         editable branch
     */
    public String verifyBranchEditing() {
        if (proof == null || tree.getRoot() == null) {
            return "no proof";
        }
        StringBuilder problems = new StringBuilder();
        if (isEditableBranchEntry(tree.getRoot().getValue())) {
            problems.append("root branch editable; ");
        }
        TreeItem<Entry> branch = findEditableBranchItem(tree.getRoot());
        if (branch == null) {
            return "SKIP (no editable branch)";
        }
        Node node = branch.getValue().node();
        String original = node.getNodeInfo().getBranchLabel();
        // F2 path: TreeViewBehavior F2 → tree.edit(selectedItem) → ProofTreeCell.startEdit
        tree.getSelectionModel().select(branch);
        int row = tree.getRow(branch);
        tree.scrollTo(row);
        tree.layout();
        tree.edit(branch);
        TreeCell<Entry> cell = cellForItem(branch);
        if (tree.getEditingItem() != branch) {
            problems.append("editing did not start; ");
        } else if (cell == null || !cell.isEditing() || !(cell.getGraphic() instanceof TextField)) {
            problems.append("cell editor not shown; ");
        } else {
            tree.edit(null);
            if (tree.getEditingItem() != null || cell.isEditing()) {
                problems.append("editing did not cancel; ");
            }
        }
        // the Swing commit path: valueForPathChanged → GUIBranchNode.setLabel
        commitBranchLabel(branch.getValue(), "WP2 verify branch");
        refresh();
        if (!"WP2 verify branch".equals(node.getNodeInfo().getBranchLabel())) {
            problems.append("label not stored; ");
        } else {
            TreeItem<Entry> after = findItem(tree.getRoot(), node);
            if (after == null || after.getValue() == null
                    || !after.getValue().displayText().contains("WP2 verify branch")) {
                problems.append("rebuilt entry text mismatch; ");
            }
        }
        // restore the original label so the demo proof stays clean
        commitBranchLabel(branch.getValue(), original);
        refresh();
        if (!original.equals(node.getNodeInfo().getBranchLabel())) {
            problems.append("restore failed; ");
        }
        boolean pass = problems.length() == 0;
        return "rootEditable=false labelEdit="
            + (pass ? "PASS" : "FAIL problems=[" + problems + "]");
    }

    /**
     * @return the first editable branch entry below (and including) the given item, or
     *         {@code null}
     */
    private static TreeItem<Entry> findEditableBranchItem(TreeItem<Entry> item) {
        if (item == null) {
            return null;
        }
        if (isEditableBranchEntry(item.getValue())) {
            return item;
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            TreeItem<Entry> result = findEditableBranchItem(child);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    /**
     * @return the rendered cell of the given tree item, or {@code null} when the row is not
     *         realized (virtual flow)
     */
    @SuppressWarnings("unchecked")
    private TreeCell<Entry> cellForItem(TreeItem<Entry> item) {
        for (javafx.scene.Node n : tree.lookupAll(".tree-cell")) {
            if (n instanceof TreeCell<?> cell && cell.getIndex() >= 0
                    && cell.getTreeItem() == item) {
                return (TreeCell<Entry>) cell;
            }
        }
        return null;
    }

    /**
     * WP-2 verification (renderer surface): asserts the leaf goal icons (Swing
     * {@code renderLeaf}), the notes marker ({@code renderNonLeaf} defaultIcon: the edit-file
     * icon) with the tooltip notes, and the NodeInfoVisualizer attachment — registering a
     * visualizer switches the node's marker to the window icon (Swing {@code WINDOW_ICON} via
     * {@code NodeInfoVisualizer.hasInstances}), the icon is actually rendered into the cell, and
     * {@code dispose()} clears the marker again. Restores the node state.
     *
     * @return a one-line report, {@code "... PASS"} if every check passes
     */
    public String verifyRendererSurface() {
        if (proof == null || tree.getRoot() == null) {
            return "no proof";
        }
        StringBuilder problems = new StringBuilder();
        StringBuilder ok = new StringBuilder();

        // the goal-state icons of the leaf rows (Swing renderLeaf: key hole variants)
        int leafIcons = countLeafIcons(tree.getRoot());
        if (leafIcons == 0) {
            problems.append("no leaf goal icons; ");
        } else {
            ok.append("leafIcons=").append(leafIcons);
        }

        TreeItem<Entry> inner = findFirstNodeItem(tree.getRoot(), false);
        if (inner == null) {
            problems.append("no inner node row; ");
        } else {
            Node node = inner.getValue().node();
            String originalNotes = node.getNodeInfo().getNotes();
            try {
                // the notes marker (Swing renderNonLeaf defaultIcon: editFile) + tooltip notes
                node.getNodeInfo().setNotes("WP2 verify note");
                tree.refresh();
                TreeItem<Entry> refreshed = findNodeEntryItem(tree.getRoot(), node);
                if (refreshed == null) {
                    problems.append("node row lost; ");
                } else {
                    if (markerKey(refreshed.getValue()) != IconFactoryF.Key.EDIT) {
                        problems.append("notes marker missing; ");
                    }
                    if (!notesOf(node).contains("WP2 verify note")) {
                        problems.append("notes tooltip text missing; ");
                    }
                    // WP-2 (NodeInfoVisualizer): the visualizer registration switches the marker
                    // to the window icon (Swing WINDOW_ICON), the listener re-renders the tree
                    NodeInfoVisualizerF visualizer =
                        new NodeInfoVisualizerF(node, "WP2 verify visualizer", "verify") {
                        };
                    if (markerKey(refreshed.getValue()) != IconFactoryF.Key.NODE_INFO_WINDOW) {
                        problems.append("visualizer marker missing; ");
                    }
                    tree.refresh();
                    TreeItem<Entry> reRefreshed = findNodeEntryItem(tree.getRoot(), node);
                    TreeCell<Entry> cell = reRefreshed == null ? null : cellForItem(reRefreshed);
                    if (cell == null || cell.getGraphic() == null) {
                        problems.append("visualizer icon not rendered; ");
                    } else {
                        ok.append(" nodeInfoVisualizer=PASS");
                    }
                    visualizer.dispose();
                    if (NodeInfoVisualizerF.hasInstances(node)) {
                        problems.append("visualizer not unregistered; ");
                    }
                    if (markerKey(refreshed.getValue()) == IconFactoryF.Key.NODE_INFO_WINDOW) {
                        problems.append("visualizer marker stale after dispose; ");
                    }
                }
            } finally {
                node.getNodeInfo().setNotes(originalNotes);
                tree.refresh();
            }
        }
        boolean pass = problems.length() == 0;
        return ok + " " + (pass ? "PASS" : "FAIL problems=[" + problems + "]");
    }

    /**
     * @param node the node to locate
     * @return the NODE entry item of the given node (branch entries whose node is the same, e.g.
     *         the root branch "Proof Tree", are skipped), or {@code null}
     */
    private static TreeItem<Entry> findNodeEntryItem(TreeItem<Entry> start, Node node) {
        if (start.getValue() != null && !start.getValue().isBranch()
                && !start.getValue().isOssChild() && start.getValue().node() == node) {
            return start;
        }
        for (TreeItem<Entry> child : start.getChildren()) {
            TreeItem<Entry> result = findNodeEntryItem(child, node);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    /** @return the number of leaf rows whose Swing-parity goal icon is rendered */
    private int countLeafIcons(TreeItem<Entry> item) {
        int count = 0;
        if (item.getValue() != null && !item.getValue().isBranch() && !item.getValue().isOssChild()
                && item.getValue().node.leaf() && markerKey(item.getValue()) != null) {
            count++;
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            count += countLeafIcons(child);
        }
        return count;
    }

    /**
     * @param wantLeaf {@code true} for the first leaf row, {@code false} for the first inner
     *        (rule application) row
     * @return the first matching node entry below (and including) the given item, or {@code null}
     */
    private static TreeItem<Entry> findFirstNodeItem(TreeItem<Entry> item, boolean wantLeaf) {
        if (item == null) {
            return null;
        }
        Entry entry = item.getValue();
        if (entry != null && !entry.isBranch() && !entry.isOssChild()
                && entry.node.leaf() == wantLeaf) {
            return item;
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            TreeItem<Entry> result = findFirstNodeItem(child, wantLeaf);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    /**
     * Returns the branch label of the given node, falling back to {@code Case <n>} and storing it
     * on the node like {@code GUIAbstractTreeNode.ensureBranchLabelIsSet}.
     */
    private static String ensureBranchLabelIsSet(Node node) {
        var nodeInfo = node.getNodeInfo();
        String label;
        if (node.root()) {
            label = "Proof Tree";
        } else {
            synchronized (nodeInfo) {
                label = nodeInfo.getBranchLabel();
                if (label == null) {
                    label = "Case " + (node.parent().getChildNr(node) + 1);
                    nodeInfo.setBranchLabel(label);
                }
            }
        }
        return label;
    }

    private void handleTreeSelection(TreeItem<Entry> item) {
        if (updatingSelection || item == null || item.getValue() == null) {
            return;
        }
        Entry entry = item.getValue();
        if (entry.isOssChild()) {
            // C21 (P3a): selecting an OSS protocol row shows a sequent modified to include the
            // transformed formula and marks the single rewriting step as the selected rule app
            // (Swing ProofTreeView GUITreeSelectionListener, ProofTreeView.java:1174-1190)
            Node ossParent = entry.node();
            if (selectionModel != null && ossParent != null && ossParent.sequent() != null) {
                var pio = entry.ossRuleApp().posInOccurrence();
                Sequent modified =
                    ossParent.sequent().replaceFormula(entry.ossFormulaNr(),
                        pio.sequentFormula()).sequent();
                selectionModel.setSelectedSequentAndRuleApp(ossParent, modified,
                    entry.ossRuleApp());
            }
            return;
        }
        Node node = entry.node();
        if (node != null && selectionModel != null && node != selectionModel.getSelectedNode()) {
            selectionModel.setSelectedNode(node);
        }
    }

    /**
     * Selects and reveals the tree item of the currently selected node, if present.
     */
    private void revealSelectedNode() {
        Node selected = selectionModel != null ? selectionModel.getSelectedNode() : null;
        if (selected == null || tree.getRoot() == null) {
            return;
        }
        TreeItem<Entry> item = findItem(tree.getRoot(), selected);
        if (item == null || tree.getSelectionModel().getSelectedItem() == item) {
            return;
        }
        selectAndReveal(item);
    }

    /**
     * Expands the ancestors of the given item, selects it and scrolls it into view.
     */
    private void selectAndReveal(TreeItem<Entry> item) {
        updatingSelection = true;
        try {
            // expand the ancestors so the item is visible
            TreeItem<Entry> a = item.getParent();
            while (a != null) {
                a.setExpanded(true);
                a = a.getParent();
            }
            tree.getSelectionModel().select(item);
            tree.scrollTo(tree.getRow(item));
        } finally {
            updatingSelection = false;
        }
    }

    private static TreeItem<Entry> findItem(TreeItem<Entry> start, Node node) {
        if (start.getValue() != null && start.getValue().node() == node) {
            return start;
        }
        for (TreeItem<Entry> child : start.getChildren()) {
            TreeItem<Entry> result = findItem(child, node);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    // -----------------------------------------------------------------------
    // Goal select above/below (menu: MP3b — Swing ProofTreeView.selectAbove/selectBelow,
    // ProofTreeView.java:550-606, invoked by GoalSelectAboveAction/GoalSelectBelowAction)
    // -----------------------------------------------------------------------

    /**
     * menu: MP3b — selects the next open goal above the currently selected node (Swing
     * {@code ProofTreeView.selectAbove}, ProofTreeView.java:550-577). The Swing version walks
     * the visible JTree rows upward from the current row: a collapsed branch row is expanded
     * while crossing it (the search continues at the far end of the just-expanded branch,
     * {@code row += newRows - prevRows}, :563-568) and the first LEAF node row is selected via
     * the selection model. JavaFX has no row API, so {@link #visibleRows()} builds the ordered
     * list of currently visible rows from the expansion state ({@code TreeItem.isExpanded()});
     * a collapsed branch is expanded (with a row-list rebuild) and the walk continues from the
     * far end of its subtree — the same behaviour as Swing.
     *
     * @return whether a goal above the current selection was found and selected
     */
    public boolean selectAbove() {
        return selectGoal(-1);
    }

    /**
     * menu: MP3b — the downward counterpart of {@link #selectAbove()} (Swing
     * {@code ProofTreeView.selectBelow}, ProofTreeView.java:584-606): a collapsed branch is
     * expanded and the walk continues at the branch row itself, moving into the expanded subtree.
     *
     * @return whether a goal below the current selection was found and selected
     */
    public boolean selectBelow() {
        return selectGoal(1);
    }

    /**
     * Walks the visible rows from the current selection in the given direction and selects the
     * first leaf row via the {@link KeYSelectionModel} (the selection listener then reveals and
     * scrolls the new selection like a user click, see {@link #revealSelectedNode}).
     */
    private boolean selectGoal(int direction) {
        TreeItem<Entry> start = tree.getSelectionModel().getSelectedItem();
        if (start == null || start.getValue() == null || tree.getRoot() == null) {
            return false;
        }
        List<TreeItem<Entry>> rows = visibleRows();
        int cursor = rows.indexOf(start);
        if (cursor < 0) {
            return false;
        }
        for (int i = cursor + direction; i >= 0 && i < rows.size(); i += direction) {
            TreeItem<Entry> item = rows.get(i);
            Entry entry = item.getValue();
            if (entry.isBranch() && isExpandableBranch(item)) {
                // Swing: expandPath(tp) — a collapsed branch is expanded while crossing it;
                // selectAbove continues at the far end of the expanded subtree
                // (ProofTreeView.java:563-568), selectBelow at the branch root (:596-598)
                item.setExpanded(true);
                rows = visibleRows();
                int branchIndex = rows.indexOf(item);
                if (direction < 0) {
                    i = branchIndex + visibleRowCount(item) - 1;
                } else {
                    i = branchIndex;
                }
                continue;
            }
            if (!entry.isBranch() && entry.node.leaf()) {
                if (selectionModel != null) {
                    selectionModel.setSelectedNode(entry.node);
                }
                return true;
            }
        }
        return false;
    }

    /**
     * @param item a branch entry
     * @return whether the branch is a real collapsed branch point that Swing would expand while
     *         walking (a {@code GUIBranchNode} whose node has a multi-child parent — the root
     *         branch is excluded by {@code parent() != null}; Swing ProofTreeView.java:560-562)
     */
    private static boolean isExpandableBranch(TreeItem<Entry> item) {
        Entry entry = item.getValue();
        return !item.isExpanded() && entry.node.parent() != null
                && entry.node.parent().childrenCount() > 1;
    }

    /**
     * @return the currently visible tree rows in display order — the FX counterpart of the
     *         Swing {@code JTree} row API used by {@code selectAbove/selectBelow}: a pre-order
     *         walk that descends only into expanded items (this mirrors the rows allocated by
     *         the {@link TreeView}, whose {@code TreeItem.expandedProperty} gates visibility)
     */
    private List<TreeItem<Entry>> visibleRows() {
        List<TreeItem<Entry>> rows = new ArrayList<>();
        TreeItem<Entry> root = tree.getRoot();
        if (root != null) {
            collectVisibleRows(root, rows);
        }
        return rows;
    }

    private static void collectVisibleRows(TreeItem<Entry> item, List<TreeItem<Entry>> into) {
        if (item == null) {
            return;
        }
        into.add(item);
        if (item.isExpanded()) {
            for (TreeItem<Entry> child : item.getChildren()) {
                collectVisibleRows(child, into);
            }
        }
    }

    /**
     * @return the number of visible rows in the subtree of the given item, the item's own row
     *         included
     */
    private static int visibleRowCount(TreeItem<Entry> item) {
        int count = 1;
        if (item.isExpanded()) {
            for (TreeItem<Entry> child : item.getChildren()) {
                count += visibleRowCount(child);
            }
        }
        return count;
    }

    // -----------------------------------------------------------------------
    // Search (Swing ProofTreeSearchBar + ProofTreeViewFilter.TreeSearchFilter)
    // -----------------------------------------------------------------------

    /**
     * Shows the search bar (Swing: {@code Ctrl+Shift+F}) and focuses the field. A query kept
     * from a previous opening is re-applied.
     */
    public void showSearchBar() {
        searchBar.setVisible(true);
        searchBar.setManaged(true);
        searchField.selectAll();
        searchField.requestFocus();
        if (!searchField.getText().isEmpty()) {
            search();
        }
    }

    /**
     * Hides the search bar and clears the query so the full tree is shown again (Swing
     * {@code setVisible(false)}).
     */
    public void hideSearchBar() {
        searchBar.setVisible(false);
        searchBar.setManaged(false);
        if (!query.isEmpty() || filterActive()) {
            query = "";
            containsMatchCache.clear();
            refresh();
        }
        tree.requestFocus();
    }

    /**
     * @return whether the collapsing search filter is currently applied to the tree structure
     */
    private boolean filterActive() {
        return searchBar.isVisible() && collapseToggle.isSelected() && !query.isEmpty();
    }

    /**
     * Runs the search for the current field text (Swing {@code search()}): reapplies the
     * collapsing filter or the cell highlights, recomputes the matches and selects the first one.
     */
    private void search() {
        search(false);
    }

    /**
     * Runs the search, optionally forcing a structural rebuild (needed when the Collapse toggle
     * flips: the filter must be applied to or removed from the tree structure).
     *
     * @param forceRebuild whether a structural rebuild is required regardless of the query change
     */
    private void search(boolean forceRebuild) {
        String newQuery = searchField.getText().toLowerCase();
        boolean queryChanged = !newQuery.equals(query);
        query = newQuery;
        if (queryChanged) {
            containsMatchCache.clear();
        }
        if (forceRebuild || (queryChanged && collapseToggle.isSelected())) {
            // structural rebuild: apply the filter, or restore the full tree when inactive
            refresh();
        } else if (queryChanged) {
            // highlight-only mode: the tree structure is unchanged, re-render the cells
            tree.refresh();
        }
        updateMatches();
        if (!matches.isEmpty()) {
            selectMatch(0);
        }
        setAlert(!query.isEmpty() && matches.isEmpty());
    }

    /** Switches to the next match (Swing {@code searchNext}), wrapping around. */
    public void searchNext() {
        if (matches.isEmpty()) {
            return;
        }
        selectMatch(matchIndex + 1 < matches.size() ? matchIndex + 1 : 0);
    }

    /** Switches to the previous match (Swing {@code searchPrevious}), wrapping around. */
    public void searchPrevious() {
        if (matches.isEmpty()) {
            return;
        }
        selectMatch(matchIndex > 0 ? matchIndex - 1 : matches.size() - 1);
    }

    private void selectMatch(int index) {
        matchIndex = index;
        TreeItem<Entry> item = matches.get(matchIndex);
        // update the selection model like a user click would (Swing setSelectionPath drives the
        // mediator, so the sequent view follows the search)
        Node node = item.getValue().node();
        if (node != null && selectionModel != null && node != selectionModel.getSelectedNode()) {
            selectionModel.setSelectedNode(node);
        }
        selectAndReveal(item);
    }

    /**
     * Recomputes {@link #matches} over the currently visible items (row order) and updates the
     * alert styling of the field.
     */
    private void updateMatches() {
        matches.clear();
        matchIndex = -1;
        if (!query.isEmpty() && tree.getRoot() != null) {
            collectMatches(tree.getRoot());
        }
        setAlert(!query.isEmpty() && matches.isEmpty());
    }

    private void collectMatches(TreeItem<Entry> item) {
        Entry entry = item.getValue();
        if (entry != null && matches(entry)) {
            matches.add(item);
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            collectMatches(child);
        }
    }

    /**
     * @param entry the entry to test
     * @return whether the entry's displayed text contains the query (case-insensitive)
     */
    private boolean matches(Entry entry) {
        return entry.displayText().toLowerCase().contains(query);
    }

    /**
     * @param node the node to test
     * @return whether the node's search text (Swing {@code TreeSearchFilter.matches}) contains
     *         the query (case-insensitive)
     */
    private boolean matches(Node node) {
        return matches(Entry.node(node));
    }

    /**
     * @param node the root of the subtree to test
     * @return whether the subtree contains a match for the query (memoized per node, Swing
     *         {@code TreeSearchFilter.containsMatch})
     */
    private boolean containsMatch(Node node) {
        Boolean cached = containsMatchCache.get(node);
        if (cached != null) {
            return cached;
        }
        boolean result = matches(Entry.node(node));
        for (int i = 0; !result && i < node.childrenCount(); i++) {
            result = containsMatch(node.child(i));
        }
        containsMatchCache.put(node, result);
        return result;
    }

    private void setAlert(boolean alert) {
        if (alert) {
            searchField.getStyleClass().add("search-alert");
        } else {
            searchField.getStyleClass().remove("search-alert");
        }
    }

    // -----------------------------------------------------------------------

    // -----------------------------------------------------------------------
    // WP-2: the renderer surface of the tree cells (Swing ProofTreeView renderer
    // renderBranch/renderLeaf/renderNonLeaf, ProofTreeView.java:1280-1424): the goal-state
    // icons, the marker icons (open node-info visualizer, notes, useless/interactive/script
    // rule applications) and the tooltip notes
    // -----------------------------------------------------------------------

    /**
     * @return the icon of the given entry (the Swing renderer's {@code style.icon}), or
     *         {@code null}. Swing paints the state color into the icon images; the FX icons use
     *         the neutral {@code key-icon} fill, the goal state is conveyed by the cell's text
     *         color class. The goal-state glyphs mirror the Swing constants: closed goal →
     *         {@code GOAL_CLOSED} (CHECK), cached-closed → LINK (Swing {@code closed-cached.png}),
     *         linked/interactive/open key holes keep the existing FX key assignments.
     */
    private javafx.scene.Node markerIcon(Entry item) {
        IconFactoryF.Key key = markerKey(item);
        return key == null ? null : IconFactoryF.createIcon(key);
    }

    /**
     * @return the marker icon key the Swing renderer would paint for the entry (the inverse gap:
     *         {@code null} when Swing paints no icon), or the verification sentinel
     */
    IconFactoryF.Key markerKey(Entry item) {
        if (item.isOssChild() || proof == null) {
            return null;
        }
        Node node = item.node;
        if (item.isBranch()) {
            // Swing renderBranch: a branch folder with at least one linked open goal below
            return hasLinkedGoalBelow(node) ? IconFactoryF.Key.LINKED_FOLDER : null;
        }
        if (node.leaf()) {
            // Swing renderLeaf: getOpenGoal is a linear scan; a closed leaf has none, skip there
            Goal goal = node.isClosed() ? null : proof.getOpenGoal(node);
            if (goal == null || node.isClosed()) {
                return node.lookup(ClosedBy.class) != null ? IconFactoryF.Key.NODE_INFO_WINDOW
                        : IconFactoryF.Key.GOAL_CLOSED;
            }
            if (goal.isLinked()) {
                return IconFactoryF.Key.KEY_HOLE_LINKED;
            }
            if (!goal.isAutomatic()) {
                return IconFactoryF.Key.KEY_HOLE_INTERACTIVE;
            }
            return IconFactoryF.Key.KEY_HOLE;
        }
        // Swing renderNonLeaf defaultIcon priority: an open node-info visualizer, notes, a
        // useless / interactive / script rule application
        if (NodeInfoVisualizerF.hasInstances(node)) {
            return IconFactoryF.Key.NODE_INFO_WINDOW;
        }
        if (node.getNodeInfo().getNotes() != null) {
            return IconFactoryF.Key.EDIT;
        }
        if (node.getNodeInfo().isUselessApplication()) {
            return IconFactoryF.Key.USELESS_APP;
        }
        if (node.getNodeInfo().getInteractiveRuleApplication()) {
            return IconFactoryF.Key.INTERACTIVE_APP;
        }
        if (node.getNodeInfo().getScriptRuleApplication()) {
            return IconFactoryF.Key.SCRIPT_APP;
        }
        return null;
    }

    /**
     * Whether some open goal below {@code branchRoot} is linked (Swing
     * {@code ProofTreeView.hasLinkedGoalBelow}, ProofTreeView.java:1311-1330: iterate the proof's
     * open goals and walk the ancestors of the linked ones instead of a breadth-first search
     * over the whole subtree).
     */
    private boolean hasLinkedGoalBelow(Node branchRoot) {
        if (proof == null) {
            return false;
        }
        for (Goal g : proof.openGoals()) {
            if (g.isLinked() && isSelfOrAncestor(branchRoot, g.node())) {
                return true;
            }
        }
        return false;
    }

    /** Whether {@code ancestor} equals {@code descendant} or is one of its transitive parents. */
    private static boolean isSelfOrAncestor(Node ancestor, Node descendant) {
        for (Node n = descendant; n != null; n = n.parent()) {
            if (n == ancestor) {
                return true;
            }
        }
        return false;
    }

    /**
     * @param node the node to check
     * @return the notes of the node and its ancestors, formatted for the tooltip (Swing
     *         {@code style.tooltip.addNotes})
     */
    private static String notesOf(Node node) {
        StringBuilder notes = new StringBuilder();
        for (Node n = node; n != null; n = n.parent()) {
            String note = n.getNodeInfo().getNotes();
            if (note != null && !note.isEmpty()) {
                notes.append(notes.length() > 0 ? "\n" : "").append("Notes: ").append(note);
            }
        }
        return notes.toString();
    }

    /**
     * The tree cell rendering: text plus the goal-state style class (Swing colors map onto the
     * theme's CSS properties). Matching rows are highlighted while a search is active. The
     * default {@code tree-cell} class is kept so the Modena selection styling applies; the state
     * and highlight classes are swapped individually on re-render.
     */
    private final class ProofTreeCell extends TreeCell<Entry> {
        private String stateClass;
        private boolean matched;

        /** the branch-label editor (WP-2 branch editing, Swing {@code DefaultTreeCellEditor}). */
        private TextField branchEditor;

        @Override
        protected void updateItem(Entry item, boolean empty) {
            super.updateItem(item, empty);
            if (!getStyleClass().contains("proof-tree-cell")) {
                getStyleClass().add("proof-tree-cell");
            }
            if (isEditing()) {
                // keep the branch-label editor visible (the re-render triggered by the edit
                // state must not replace it)
                return;
            }
            // WP-2: Swing DefaultTreeCellEditor.isCellEditable (ProofTreeView.java:243-270) —
            // only branch nodes whose node has a parent are editable; the per-cell editable flag
            // makes TreeCell.startEdit (and therefore the F2 binding) deny the rest
            setEditable(item != null && item.isBranch() && item.node != null
                    && item.node.parent() != null);
            renderStatic(item, empty);
        }

        @Override
        public void startEdit() {
            super.startEdit();
            if (!isEditing()) {
                // denied by the editable gate (Swing isCellEditable parity)
                return;
            }
            if (branchEditor == null) {
                branchEditor = new TextField();
                branchEditor.setOnAction(event -> commitBranchEditor());
                branchEditor.setOnKeyPressed(event -> {
                    if (KeyCode.ESCAPE.equals(event.getCode())) {
                        event.consume();
                        cancelEdit();
                    }
                });
                // Swing delegateView.setInvokesStopCellEditing(true): a focus loss commits
                branchEditor.focusedProperty().addListener((obs, was, now) -> {
                    if (!now && isEditing()) {
                        commitBranchEditor();
                    }
                });
            }
            setText(null);
            setTooltip(null);
            branchEditor.setText(getItem() == null ? "" : getItem().displayText());
            setGraphic(branchEditor);
            branchEditor.selectAll();
            branchEditor.requestFocus();
        }

        @Override
        public void cancelEdit() {
            super.cancelEdit();
            // restore the static rendering (the edit state re-render keeps the static content)
            renderStatic(getItem(), getItem() == null);
        }

        /**
         * Ends the editing state and applies the typed label through the Swing commit seam
         * ({@code GUIProofTreeModel.valueForPathChanged → GUIBranchNode.setLabel}).
         */
        private void commitBranchEditor() {
            Entry entry = getItem();
            String text = branchEditor.getText();
            cancelEdit();
            if (entry != null && entry.isBranch()) {
                commitBranchLabel(entry, text);
            }
        }

        private void renderStatic(Entry item, boolean empty) {
            if (stateClass != null) {
                getStyleClass().remove(stateClass);
                stateClass = null;
            }
            if (matched) {
                getStyleClass().remove("proof-tree-match");
                matched = false;
            }
            if (empty || item == null) {
                setText(null);
                setTooltip(null);
                // clear the inline styles and the icon of a reused cell (the WP-5 stylers may
                // have styled / the WP-2 renderer surface may have iconized the entry that was
                // shown before)
                setStyle(null);
                setGraphic(null);
                return;
            }
            setText(item.displayText());
            stateClass = styleClassOf(item);
            getStyleClass().add(stateClass);
            matched = !query.isEmpty() && matches(item);
            if (matched) {
                getStyleClass().add("proof-tree-match");
            }
            // WP-5: the extension stylers (Swing renderer stylers parity) accumulate their
            // border/background colors and tooltip title; the css is applied inline and wins
            // over the theme's goal-state classes, like the Swing renderer's last-writer style
            Style style = null;
            if (!cellStylers.isEmpty()) {
                style = new Style();
                for (CellStyler styler : cellStylers) {
                    styler.style(style, item);
                }
            }
            String css = style == null ? "" : style.css();
            setStyle(css.isEmpty() ? null : css);
            // WP-2 (renderer surface): the goal-state and marker icons of the Swing renderer
            // (ProofTreeView.renderLeaf/renderBranch/renderNonLeaf, ProofTreeView.java:1280-1424)
            setGraphic(markerIcon(item));
            // menu: MP3a — proof-tree tooltips are gated by the shared ViewSettings flag "Show
            // Tooltips in Proof Tree" (Swing ProofTreeView.getToolTipText,
            // ProofTreeView.java:195-217 renders no tooltip unless isShowProofTreeTooltips()).
            // The cell re-consults the flag on every updateItem; the View-menu toggle triggers a
            // refresh() (MainWindowF.buildViewMenu) so the change applies immediately. Minimal
            // fidelity: the Swing renderer builds a rich styled tooltip (rule name, position in
            // occurrence, notes, rendered by ProofTreeView.renderTooltip :1202-1219); the FX cell
            // shows the WP-2 renderer-surface text (notes, useless analysis) — or the title a
            // styler set (WP-5, Swing Style.tooltip parity).
            if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .isShowProofTreeTooltips()) {
                setTooltip(new Tooltip(
                    style != null && style.getTooltipTitle() != null ? style.getTooltipTitle()
                            : tooltipText(item)));
            } else {
                setTooltip(null);
            }
        }

        private String styleClassOf(Entry item) {
            if (item.isOssChild()) {
                // C21 (P3a): OSS protocol rows render styled like a branch decoration
                return "proof-tree-oss-child";
            }
            Node node = item.node;
            if (item.isBranch()) {
                return node.isClosed() ? "proof-tree-branch-closed" : "proof-tree-branch";
            }
            if (node.leaf()) {
                if (node.isClosed()) {
                    return "proof-tree-closed";
                }
                Goal goal = proof != null ? proof.getOpenGoal(node) : null;
                if (goal == null) {
                    return "proof-tree-closed";
                }
                return goal.isAutomatic() ? "proof-tree-open" : "proof-tree-interactive";
            }
            if (node.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp) {
                // C21: the One Step Simplifier node itself (Swing renders it like a rule
                // application node; the protocol rows are its children)
                return "proof-tree-oss";
            }
            return "proof-tree-inner";
        }

        private String tooltipText(Entry item) {
            if (item.isBranch()) {
                return "Branch: " + item.branchLabel;
            }
            if (item.isOssChild()) {
                // C21: Swing GUIOneStepChildTreeNode.getSearchString shows the applied rule and
                // the pretty-printed sub-term; the tooltip mirrors it without the term printer
                return "One Step Simplification step: " + item.displayText();
            }
            // menu: MP3a — the node's applied rule name (Swing rule-application nodes show the
            // applied rule, ProofTreeView.java:1389), falling back to the plain node serial.
            Node node = item.node;
            RuleApp appliedRule = node.getAppliedRuleApp();
            StringBuilder text = new StringBuilder();
            if (appliedRule != null) {
                text.append("Node ").append(node.serialNr()).append(": ")
                        .append(appliedRule.rule().name());
            } else {
                text.append("Node ").append(node.serialNr());
            }
            // WP-2 (renderer surface): the Swing tooltip carries the node's notes and the
            // "useless application" analysis (ProofTreeView.renderLeaf/renderNonLeaf →
            // style.tooltip.addNotes, ProofTreeView.java:1374-1377/:1400)
            String notes = notesOf(node);
            if (!notes.isEmpty()) {
                text.append('\n').append(notes);
            }
            if (node.getNodeInfo().isUselessApplication()) {
                text.append("\nAnalysis: Not required to close proof");
            }
            return text.toString();
        }
    }
}
