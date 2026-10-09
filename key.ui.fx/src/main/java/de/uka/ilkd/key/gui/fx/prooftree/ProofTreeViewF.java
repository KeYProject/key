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
import java.util.concurrent.atomic.AtomicInteger;
import javafx.geometry.Insets;
import javafx.scene.control.Button;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.ContextMenu;
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

import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.prover.rules.RuleApp;
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
public class ProofTreeViewF extends BorderPane {

    private static final Logger LOGGER = LoggerFactory.getLogger(ProofTreeViewF.class);

    private static final KeyCombination OPEN_SEARCH =
        new KeyCodeCombination(KeyCode.F, KeyCombination.CONTROL_DOWN, KeyCombination.SHIFT_DOWN);

    /**
     * One tree entry: either a proof node entry (a rule application) or a branch entry (labeled
     * sub-tree; {@code node} is the root of the branch).
     */
    public static final class Entry {
        final Node node;
        final String branchLabel;

        private Entry(Node node, String branchLabel) {
            this.node = node;
            this.branchLabel = branchLabel;
        }

        static Entry node(Node node) {
            return new Entry(node, null);
        }

        static Entry branch(Node node, String label) {
            return new Entry(node, Objects.requireNonNull(label));
        }

        public boolean isBranch() {
            return branchLabel != null;
        }

        public Node node() {
            return node;
        }

        /**
         * @return the text shown for this entry, whitespace-normalized like the Swing renderer
         */
        public String displayText() {
            if (branchLabel != null) {
                return branchLabel;
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
            if (oldProof != null) {
                oldProof.removeProofTreeListener(proofTreeListener);
            }
            if (newProof != null) {
                newProof.addProofTreeListener(proofTreeListener);
            }
            liveEventCount.set(0);
            liveRefreshCount.set(0);
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
        int[] counters = { 0, 0 }; // node entries, branch entries
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
            + seen.size() + " branches=" + counters[1] + (filtersActive ? " filtered" : "")
            + " " + (pass ? "PASS" : "FAIL");
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

    /** @return the number of entries (node + branch) currently displayed */
    private int countEntries() {
        int[] counters = { 0, 0 };
        collect(tree.getRoot(), Collections.newSetFromMap(new IdentityHashMap<>()), counters);
        return counters[0] + counters[1];
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
            seen.add(entry.node);
            if (entry.isBranch()) {
                counters[1]++;
            } else {
                counters[0]++;
            }
        }
        for (TreeItem<Entry> child : item.getChildren()) {
            collect(child, seen, counters);
        }
    }

    private TreeItem<Entry> buildBranch(Node branchRoot, String label) {
        TreeItem<Entry> branchItem = new TreeItem<>(Entry.branch(branchRoot, label));

        // collect the branch's linear chain first (mirrors GUIBranchNode.fillChildrenCache)
        List<Node> chain = new ArrayList<>();
        Node current = branchRoot;
        while (true) {
            chain.add(current);
            if (current.childrenCount() == 1) {
                current = current.child(0);
                continue;
            }
            break;
        }
        boolean searchActive = filterActive();
        // Swing: while the collapsing search is active it takes precedence over the
        // intermediate-step filters (GUIProofTreeModel.bypassNodeFilter)
        boolean nodeFilterActive =
            !searchActive && (hideIntermediateSteps() || hideAutomodeSteps());
        int branchCount = current.childrenCount();

        if (!nodeFilterActive) {
            // all chain steps, search-filtered
            for (Node node : chain) {
                if (!searchActive || matches(node)) {
                    branchItem.getChildren().add(new TreeItem<>(Entry.node(node)));
                }
            }
        } else if (hideIntermediateSteps()) {
            // Hide Intermediate Proofsteps: a branch shows only the last element of its
            // [chain..., branch folders...] list (the Swing NodeFilter shows the child at the
            // last position); with branch folders below, the whole chain — including the split
            // step — is hidden, without them the chain's final node (the goal) remains
            if (branchCount == 0) {
                branchItem.getChildren()
                        .add(new TreeItem<>(Entry.node(chain.get(chain.size() - 1))));
            }
        } else {
            // Hide Non-interactive Proofsteps: interactive steps stay visible, plus the final
            // node of leaf chains
            for (int i = 0; i < chain.size(); i++) {
                Node node = chain.get(i);
                boolean last = i == chain.size() - 1;
                if (node.getNodeInfo().getInteractiveRuleApplication()
                        || last && branchCount == 0) {
                    branchItem.getChildren().add(new TreeItem<>(Entry.node(node)));
                }
            }
        }

        // at a branch point (or a leaf): one branch item per child, pruned by the global filters.
        // Read by index instead of iterating the live children list: the prover thread may add
        // children concurrently (ArrayList view); a concurrent mutation is healed by the next
        // structural event.
        for (int i = 0; i < branchCount; i++) {
            Node child = current.child(i);
            if (searchActive && !containsMatch(child)) {
                // the subtree contains no match: hidden (Swing TreeSearchFilter.showSubtree)
                continue;
            }
            if (hiddenByGlobalFilters(child)) {
                continue;
            }
            branchItem.getChildren().add(buildBranch(child, ensureBranchLabelIsSet(child)));
        }
        return branchItem;
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
     * Builds the right-click context menu: the two mutually exclusive node filters and the two
     * independently toggleable global filters, like the Swing dockable's "Settings" menu, plus
     * the expand/collapse and sibling actions of the Swing proof tree popup menu
     * ({@code ProofTreePopupFactory}). The action items that need prover control (Run Strategy
     * On Node, Prune, Notes, goals enablement, statistics) arrive with the M3 action framework.
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
        ContextMenu menu = new ContextMenu(hideIntermediateItem, onlyInteractiveItem,
            new SeparatorMenuItem(), hideClosedItem, hideInteractiveItem, new SeparatorMenuItem(),
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
            actionItem("Set All Goals Below to Automatic", null, () -> setGoalsBelow(true)));
        menu.setOnShowing(e -> {
            // pick up changes made elsewhere (e.g. by the classic UI sharing the settings)
            hideIntermediateItem.setSelected(hideIntermediateSteps());
            onlyInteractiveItem.setSelected(hideAutomodeSteps());
            hideClosedItem.setSelected(hideClosedSubtrees());
            hideInteractiveItem.setSelected(hideInteractiveGoals());
        });
        return menu;
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

    /** Expands every branch below the given item (Swing Expand All Below). */
    private void expandAllBelow(TreeItem<Entry> item) {
        if (item == null) {
            return;
        }
        expandRec(item);
    }

    private static void expandRec(TreeItem<Entry> item) {
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
        Node node = item.getValue().node();
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
        return matches(new Entry(node, null));
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
        boolean result = matches(new Entry(node, null));
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
            return "proof-tree-inner";
        }

        private String tooltipText(Entry item) {
            if (item.isBranch()) {
                return "Branch: " + item.branchLabel;
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
