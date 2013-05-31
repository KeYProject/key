// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.prooftree;

import de.uka.ilkd.key.gui.SearchBar;
import java.util.Vector;

import javax.swing.event.DocumentEvent;
import javax.swing.event.TreeModelEvent;
import javax.swing.event.TreeModelListener;
import javax.swing.text.Position;
import javax.swing.tree.TreePath;

class ProofTreeSearchBar
        extends SearchBar implements TreeModelListener {

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
        startRow = currentRow + 1;
        startRow %= cache.size();
        search(searchField.getText(), Position.Bias.Forward);
    }

    public void searchPrevious() {
        fillCache();
        startRow = currentRow - 1;
        startRow %= cache.size();
        search(searchField.getText(), Position.Bias.Backward);
    }
    
    public boolean search(String searchString){
        return search(searchString, Position.Bias.Forward);
    }

    private synchronized boolean search(String searchString, 
            Position.Bias direction) {
        if (searchString.equals("")) {
            startRow = 0;
        }
        currentRow = getNextMatch(searchString,
                startRow, direction);
        GUIAbstractTreeNode node = null;
        TreePath tp = null;
        if (currentRow != -1) {
            node = cache.get(currentRow);
            tp = new TreePath(node.getPath());
        }
        if (node != null && node instanceof GUIBranchNode) {
            this.proofTreeView.selectBranchNode((GUIBranchNode)node);
        } else {
            this.proofTreeView.delegateView.scrollPathToVisible(tp);
            this.proofTreeView.delegateView.setSelectionPath(tp);
        }
        return (currentRow != -1);
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
        if (cache == null) {
            cache = new Vector<GUIAbstractTreeNode>();
            if (this.proofTreeView.delegateModel.getRoot() != null) {
                cache.add((GUIAbstractTreeNode) this.proofTreeView.delegateModel.getRoot());
                fillCacheHelp((GUIBranchNode) this.proofTreeView.delegateModel.getRoot());
            }
        }
    }

    private void fillCacheHelp(GUIBranchNode branch) {
        if (branch == null) return;
        GUIAbstractTreeNode n;
        for (int i = 0; i < this.proofTreeView.delegateModel.getChildCount(branch); i++) {
            n = (GUIAbstractTreeNode)this.proofTreeView.delegateModel.getChild(branch, i);
            cache.add(n);
            if (n instanceof GUIBranchNode)
                    fillCacheHelp((GUIBranchNode)n);
        }
    }

    private int getNextMatch(String searchString, int startingRow,
            Position.Bias bias) {
        fillCache();
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