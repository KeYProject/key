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
        return "proofNodes=" + proofNodeCount + " nodeEntries=" + counters[0] + " unique="
            + seen.size() + " branches=" + counters[1] + " " + (pass ? "PASS" : "FAIL");
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

        Node current = branchRoot;
        // linear walk along single-child nodes, mirroring GUIBranchNode.fillChildrenCache
        while (true) {
            if (!filterActive() || matches(current)) {
                branchItem.getChildren().add(new TreeItem<>(Entry.node(current)));
            }
            if (current.childrenCount() == 1) {
                current = current.child(0);
                continue;
            }
            break;
        }
        // at a branch point (or a leaf): one branch item per child. Read by index instead of
        // iterating the live children list: the prover thread may add children concurrently
        // (ArrayList view); a concurrent mutation is healed by the next structural event.
        int branchCount = current.childrenCount();
        for (int i = 0; i < branchCount; i++) {
            Node child = current.child(i);
            if (filterActive() && !containsMatch(child)) {
                // the subtree contains no match: hidden (Swing TreeSearchFilter.showSubtree)
                continue;
            }
            branchItem.getChildren().add(buildBranch(child, ensureBranchLabelIsSet(child)));
        }
        return branchItem;
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
            setTooltip(new Tooltip(tooltipText(item)));
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
            return "Node " + item.node.serialNr();
        }
    }
}
