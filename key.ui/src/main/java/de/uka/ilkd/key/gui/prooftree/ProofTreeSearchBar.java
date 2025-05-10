/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.util.ArrayList;
import java.util.List;
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

    public ProofTreeSearchBar(ProofTreeView proofTreeView) {
        this.proofTreeView = proofTreeView;
    }

    @Override
    public void setVisible(boolean vis) {
        super.setVisible(vis);
        if (!vis && proofTreeView != null) {
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
        fillCache();
        return search(searchString, Position.Bias.Forward);
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
    }

    private void addNodeToCache(GUIAbstractTreeNode node) {
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
