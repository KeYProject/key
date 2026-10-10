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
import java.util.concurrent.atomic.AtomicInteger;
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
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
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
 * Deliberately deferred to later M2/M3 chunks: the further filters ({@code
 * HIDE_CLOSED_SUBTREES}, {@code HIDE_INTERACTIVE_GOALS}), heatmap, notes/tooltips of the rich
 * Swing renderer, one-step-simplifier protocol children, lazy population for very large proofs
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
     * The context menu shown on right click: the filter toggles (Swing keeps these checkboxes in
     * the dockable's "Settings" menu, which the FX docking framework does not have yet) plus the
     * expand/collapse and sibling actions of the Swing proof tree popup menu
     * (ProofTreePopupFactory). The state lives in {@link ProofIndependentSettings} like in Swing,
     * so it persists and is shared with the classic UI.
     */
    private final ContextMenu contextMenu = createContextMenu();

    /**
     * The branch entry the popup actions apply to, resolved when the menu opens: the selected
     * entry itself if it is a branch, otherwise its parent — like the Swing popup's
     * {@code context.branch}.
     */
    private TreeItem<Entry> popupBranchItem;

    /** the node the popup was invoked on (Swing {@code ProofTreeContext.invokedNode}) */
    private Node popupNode;

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
     * Creates an empty proof tree view.
     */
    public ProofTreeViewF() {
        tree.getStyleClass().add("proof-tree");
        tree.setCellFactory(view -> new ProofTreeCell());
        tree.getSelectionModel().selectedItemProperty()
                .addListener((obs, oldItem, newItem) -> handleTreeSelection(newItem));
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
            TreeItem<Entry> selected = tree.getSelectionModel().getSelectedItem();
            TreeItem<Entry> item = selected != null ? selected : tree.getRoot();
            if (item != null) {
                // Swing ProofTreeContext: the invoked node is the clicked entry's node, for node
                // entries and branch entries alike; the branch item is its parent for node entries
                popupNode = item.getValue().node();
                if (!item.getValue().isBranch()) {
                    item = item.getParent();
                }
            }
            popupBranchItem = item;
            contextMenu.show(tree, e.getScreenX(), e.getScreenY());
            e.consume();
        });
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
     * and P3a's Show Subtree Statistics. Delayed Cut (feature-flagged) and the macro submenu
     * (B12, P3b) are not yet ported; the PROOF_TREE extension contributions belong to P4 (C24).
     */
    private ContextMenu createContextMenu() {
        CheckMenuItem hideIntermediateItem = new CheckMenuItem("Hide Intermediate Proofsteps");
        hideIntermediateItem.setSelected(hideIntermediateSteps());
        CheckMenuItem onlyInteractiveItem = new CheckMenuItem("Hide Non-interactive Proofsteps");
        onlyInteractiveItem.setSelected(hideAutomodeSteps());
        // Swing keeps only one node filter active: activating one deactivates the other
        hideIntermediateItem.setOnAction(e -> {
            setHideIntermediateSteps(hideIntermediateItem.isSelected());
            if (hideIntermediateItem.isSelected() && hideAutomodeSteps()) {
                setHideAutomodeSteps(false);
                onlyInteractiveItem.setSelected(false);
            }
            refresh();
        });
        onlyInteractiveItem.setOnAction(e -> {
            setHideAutomodeSteps(onlyInteractiveItem.isSelected());
            if (onlyInteractiveItem.isSelected() && hideIntermediateSteps()) {
                setHideIntermediateSteps(false);
                hideIntermediateItem.setSelected(false);
            }
            refresh();
        });
        CheckMenuItem hideClosedItem = new CheckMenuItem("Hide Closed Subtrees");
        hideClosedItem.setSelected(hideClosedSubtrees());
        hideClosedItem.setOnAction(e -> {
            setHideClosedSubtrees(hideClosedItem.isSelected());
            refresh();
        });
        CheckMenuItem hideInteractiveItem =
            new CheckMenuItem("Hide Subtrees Whose Goals are Interactive");
        hideInteractiveItem.setSelected(hideInteractiveGoals());
        hideInteractiveItem.setOnAction(e -> {
            setHideInteractiveGoals(hideInteractiveItem.isSelected());
            refresh();
        });
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
            new SeparatorMenuItem(), subtreeStatsItem);
        menu.setOnShowing(e -> {
            // pick up changes made elsewhere (e.g. by the classic UI sharing the settings)
            hideIntermediateItem.setSelected(hideIntermediateSteps());
            onlyInteractiveItem.setSelected(hideAutomodeSteps());
            hideClosedItem.setSelected(hideClosedSubtrees());
            hideInteractiveItem.setSelected(hideInteractiveGoals());
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

    /**
     * The tree cell rendering: text plus the goal-state style class (Swing colors map onto the
     * theme's CSS properties). Matching rows are highlighted while a search is active. The
     * default {@code tree-cell} class is kept so the Modena selection styling applies; the state
     * and highlight classes are swapped individually on re-render.
     */
    private final class ProofTreeCell extends TreeCell<Entry> {
        private String stateClass;
        private boolean matched;

        @Override
        protected void updateItem(Entry item, boolean empty) {
            super.updateItem(item, empty);
            if (!getStyleClass().contains("proof-tree-cell")) {
                getStyleClass().add("proof-tree-cell");
            }
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
                return;
            }
            setText(item.displayText());
            stateClass = styleClassOf(item);
            getStyleClass().add(stateClass);
            matched = !query.isEmpty() && matches(item);
            if (matched) {
                getStyleClass().add("proof-tree-match");
            }
            // menu: MP3a — proof-tree tooltips are gated by the shared ViewSettings flag "Show
            // Tooltips in Proof Tree" (Swing ProofTreeView.getToolTipText,
            // ProofTreeView.java:195-217 renders no tooltip unless isShowProofTreeTooltips()).
            // The cell re-consults the flag on every updateItem; the View-menu toggle triggers a
            // refresh() (MainWindowF.buildViewMenu) so the change applies immediately. Minimal
            // fidelity: the Swing renderer builds a rich styled tooltip (rule name, position in
            // occurrence, notes, rendered by ProofTreeView.renderTooltip :1202-1219); the FX cell
            // shows the node/rule name only.
            if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .isShowProofTreeTooltips()) {
                setTooltip(new Tooltip(tooltipText(item)));
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
            if (appliedRule != null) {
                return "Node " + node.serialNr() + ": " + appliedRule.rule().name();
            }
            return "Node " + node.serialNr();
        }
    }
}
