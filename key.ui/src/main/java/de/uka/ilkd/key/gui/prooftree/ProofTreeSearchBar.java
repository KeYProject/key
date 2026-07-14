/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.util.ArrayList;
import java.util.List;
import javax.swing.JToggleButton;
import javax.swing.SwingUtilities;
import javax.swing.event.TreeModelEvent;
import javax.swing.event.TreeModelListener;
import javax.swing.text.Position;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.gui.SearchBar;

import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NonNull;

class ProofTreeSearchBar extends SearchBar implements TreeModelListener {
    private final ProofTreeView proofTreeView;
    private int startRow = 0;
    private int currentRow = 0;

    /**
     * When selected, searching collapses the proof tree to the matches (and the branch structure
     * needed to reach them); when deselected, the search only highlights matches without hiding
     * anything. Created in {@link #createUI()}.
     */
    private JToggleButton collapseToggle;

    /** whether the {@link ProofTreeViewFilter#SEARCH} filter is currently applied to the model */
    private boolean filterApplied = false;

    /** whether a deferred re-expansion of the filtered tree is already pending */
    private boolean reexpandScheduled = false;

    public ProofTreeSearchBar(ProofTreeView proofTreeView) {
        this.proofTreeView = proofTreeView;
    }

    @Override
    public void createUI() {
        super.createUI();
        collapseToggle = new JToggleButton("Collapse", true);
        collapseToggle.setToolTipText(
            "Collapse the proof tree to the search matches (otherwise only highlight them)");
        collapseToggle.setMargin(new java.awt.Insets(2, 4, 2, 4));
        collapseToggle.addActionListener(e -> search());
        add(collapseToggle);
    }

    @Override
    public void setVisible(boolean vis) {
        super.setVisible(vis);
        if (vis) {
            // re-apply the collapsing filter for a search term kept from a previous opening
            if (!searchField.getText().isEmpty()) {
                search();
            }
        } else if (proofTreeView != null) {
            updateCollapsingFilter("");
            proofTreeView.delegateView.requestFocusInWindow();
        }
    }

    public void searchNext() {
        fillCache();
        if (cache.isEmpty()) {
            return; // no results to switch to
        }
        startRow = currentRow + 1;
        startRow %= cache.size();
        search(searchField.getText(), Position.Bias.Forward);
    }

    public void searchPrevious() {
        fillCache();
        if (cache.isEmpty()) {
            return; // no results to switch to
        }
        startRow = currentRow - 1;
        startRow %= cache.size();
        search(searchField.getText(), Position.Bias.Backward);
    }

    public boolean search(@NonNull String searchString) {
        updateCollapsingFilter(searchString);
        fillCache();
        return search(searchString, Position.Bias.Forward);
    }

    /**
     * Updates the {@link ProofTreeViewFilter#SEARCH} filter with the given query, hiding subtrees
     * (and intermediate steps) that contain no match so that the proof tree collapses to the
     * relevant branches while searching. Does nothing but deactivate the filter when the
     * {@link #collapseToggle} is off, so the search merely highlights matches.
     *
     * @param searchString the current content of the search field.
     */
    private void updateCollapsingFilter(@NonNull String searchString) {
        GUIProofTreeModel delegateModel = this.proofTreeView.getDelegateModel();
        if (delegateModel == null) {
            return;
        }
        boolean collapse = collapseToggle != null && collapseToggle.isSelected()
                && !searchString.isEmpty();
        if (collapse) {
            ProofTreeViewFilter.SEARCH.setQuery(searchString);
            delegateModel.setFilter(ProofTreeViewFilter.SEARCH, true);
            filterApplied = true;
            // The filter just reset the tree structure (collapsing it); expand the now-small
            // filtered tree so that all surviving matches are revealed without manual expansion.
            proofTreeView.expandFilteredTree();
        } else if (filterApplied) {
            // Only remove the filter (rebuilding the tree) when it was actually applied, so the
            // highlight-only mode does not rebuild on every keystroke. Clear the flag first so the
            // structure change from removing the filter does not trigger a re-expansion (see
            // reset()).
            filterApplied = false;
            ProofTreeViewFilter.SEARCH.setQuery("");
            delegateModel.setFilter(ProofTreeViewFilter.SEARCH, false);
            // The rebuild dropped the selection; restore it so e.g. the view filters stay usable.
            proofTreeView.selectCurrentNodeInTree();
        }
    }

    private synchronized boolean search(String searchString, Position.Bias direction) {
        if (searchString.isEmpty()) {
            startRow = 0;
        }
        currentRow = getNextMatch(searchString, startRow, direction);
        GUIAbstractTreeNode node = null;
        TreePath tp = null;
        if (currentRow != -1) {
            node = cache.get(currentRow).first;
            tp = new TreePath(node.getPath());
        }
        if (node instanceof GUIBranchNode) {
            tp = this.proofTreeView.selectBranchNode((GUIBranchNode) node);
        }

        this.proofTreeView.delegateView.scrollPathToVisible(tp);
        this.proofTreeView.delegateView.setSelectionPath(tp);

        return currentRow != -1;
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

    private List<Pair<GUIAbstractTreeNode, String>> cache;

    public synchronized void reset() {
        cache = null;
        // The proof tree changed (e.g. a strategy run added nodes). If the collapsing search is
        // active, the rebuilt tree is collapsed again; re-expand it so newly matching nodes become
        // visible. Deferred to run after the current tree-change event has been processed.
        if (filterApplied && !reexpandScheduled) {
            reexpandScheduled = true;
            SwingUtilities.invokeLater(() -> {
                reexpandScheduled = false;
                if (filterApplied) {
                    proofTreeView.expandFilteredTree();
                }
            });
        }
    }

    private void addNodeToCache(GUIAbstractTreeNode node) {
        cache.add(new Pair<>(node, node.getSearchString().toLowerCase()));
    }

    private void addNodeToCache(@NonNull GUIAbstractTreeNode node) {
        cache.add(new Pair<>(node, node.getSearchString().toLowerCase()));
    }

    private void fillCache() {
        if (cache == null) {
            cache = new ArrayList<>();
            final GUIProofTreeModel delegateModel = this.proofTreeView.getDelegateModel();
            if (delegateModel != null
                    && delegateModel.getRoot() != null) {
                addNodeToCache((GUIAbstractTreeNode) delegateModel.getRoot());
                fillCacheHelp((GUIBranchNode) delegateModel.getRoot());
            }
        }
    }

    private void fillCacheHelp(GUIBranchNode branch) {
        if (branch == null) {
            return;
        }
        final GUIProofTreeModel delegateModel = this.proofTreeView.getDelegateModel();
        for (int i = 0; i < delegateModel.getChildCount(branch); i++) {
            final GUIAbstractTreeNode n = (GUIAbstractTreeNode) delegateModel.getChild(branch, i);
            addNodeToCache(n);
            if (n instanceof GUIBranchNode branchNode) {
                fillCacheHelp(branchNode);
            }
        }
    }

    private int getNextMatch(@NonNull String searchString, int startingRow, Position.Bias bias) {
        String s = searchString.toLowerCase();

        if (bias == Position.Bias.Forward) {
            if (startingRow < 0) {
                startingRow = 0;
            }
            for (int i = startingRow; i < cache.size(); i++) {
                if (nodeContainsString(i, s)) {
                    return i;
                }
            }
            for (int i = 0; i < startingRow && i < cache.size(); i++) {
                if (nodeContainsString(i, s)) {
                    return i;
                }
            }
        } else {
            if (startingRow > cache.size() - 1) {
                startingRow = cache.size() - 1;
            }
            for (int i = startingRow; i >= 0; i--) {
                if (nodeContainsString(i, s)) {
                    return i;
                }
            }
            for (int i = cache.size() - 1; i > startingRow && i > 0; i--) {
                if (nodeContainsString(i, s)) {
                    return i;
                }
            }
        }
        return -1;
    }

    /**
     * returns true if <tt>searchString</tt> is contained in the lowercase search string of the node
     *
     * @param node the node index in the cache
     * @param searchString the String to be looked for
     * @return true if a match has been found
     */
    private boolean nodeContainsString(int node, @NonNull String searchString) {
        return cache.get(node).second.contains(searchString);
    }
}
