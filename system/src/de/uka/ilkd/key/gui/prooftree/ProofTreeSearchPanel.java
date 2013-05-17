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

/**
 * 
 */
package de.uka.ilkd.key.gui.prooftree;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.util.Vector;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;
import javax.swing.KeyStroke;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.event.TreeModelEvent;
import javax.swing.event.TreeModelListener;
import javax.swing.text.Position;
import javax.swing.tree.TreePath;

class ProofTreeSearchPanel extends JPanel implements DocumentListener,
        TreeModelListener {

    private final ProofTreeView proofTreeView;
    private static final long serialVersionUID = -1945019325314041986L;
    private JTextField searchString = new JTextField(20);
    private JButton prev = new JButton("Prev ");
    private JButton next = new JButton("Next");
    private JPanel panel = new JPanel();        
    private JButton close = new JButton("Close");
    private int startRow = 0;
    private int currentRow = 0;
    private Position.Bias direction = Position.Bias.Forward;
    
    private ActionListener closePanel = new ActionListener() {
        public void actionPerformed(ActionEvent actionEvent) {
            setVisible(false);
        }
    };
    private ActionListener search = new ActionListener() {
        public void actionPerformed(ActionEvent e) {
            if (e.getSource() == next) {        
                direction = Position.Bias.Forward;
                searchString.requestFocusInWindow();
            } else if (e.getSource() == prev) {
                direction = Position.Bias.Backward;
                searchString.requestFocusInWindow();
            } else {
                // if e.g. called by pressing enter, perform a forward search
                direction = Position.Bias.Forward;
            }
            searchNext();
        }
    };

    public ProofTreeSearchPanel(ProofTreeView proofTreeView) {
        this.proofTreeView = proofTreeView;
        registerKeyboardAction(closePanel, KeyStroke
            .getKeyStroke(KeyEvent.VK_ESCAPE, 0), JComponent
            .WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        registerKeyboardAction(search, KeyStroke
            .getKeyStroke(KeyEvent.VK_ENTER, 0), JComponent
            .WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        searchString.getDocument().addDocumentListener(this);
        prev.addActionListener(search);
        next.addActionListener(search);
        close.addActionListener(closePanel);
        
        setLayout(new BorderLayout());
        add(searchString, BorderLayout.NORTH);
        panel.setLayout(new BoxLayout(panel, BoxLayout.LINE_AXIS));
        panel.add(new JLabel("Search"));
        panel.add(Box.createHorizontalGlue());
        panel.add(prev);
        panel.add(next);
        panel.add(Box.createHorizontalGlue());
        panel.add(close);
        add(panel, BorderLayout.SOUTH);
        super.setVisible(false);
    }

    public void setVisible(boolean vis) {
        super.setVisible(vis);
        if (vis) {
            searchString.selectAll();
            searchString.requestFocusInWindow();
        } else {
            this.proofTreeView.delegateView.requestFocusInWindow();
        }
    }
    
    public void requestFocus() {
    	searchString.requestFocus();
    }

    private synchronized void searchNext() {
        if (cache == null) fillCache();
        if (direction == Position.Bias.Forward) {
            if (currentRow + 1 < cache.size()) {
                startRow = currentRow + 1;
            } else {
                startRow = 0;
            }
        } else {
            if (currentRow - 1 >= 0) {
                startRow = currentRow - 1;
            } else {
                startRow = cache.size() - 1;
            }
        }
        search();
    }

    private synchronized void search() {
        if (searchString.getText().equals("")) {
                startRow = 0;
        }
        currentRow = getNextMatch(searchString.getText(),
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
        cache = new Vector<GUIAbstractTreeNode>();
        if (this.proofTreeView.delegateModel.getRoot() != null) {
            cache.add((GUIAbstractTreeNode)this.proofTreeView.delegateModel.getRoot());
            fillCacheHelp((GUIBranchNode)this.proofTreeView.delegateModel.getRoot());
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
        if (cache == null) fillCache();
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