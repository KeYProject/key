// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.prooftree;


import java.lang.ref.WeakReference;
import java.util.Enumeration;
import java.util.LinkedList;

import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;


public abstract class GUIAbstractTreeNode implements TreeNode {

    private GUIProofTreeModel tree;

    // made weak otherwise there are leaks in ExpansionState.map 
    // and ProofTreeView.delegateView.lastPathComponent 
    private WeakReference<Node> noderef;

    protected GUIProofTreeModel getProofTreeModel () {
	return tree;
    }

    public GUIAbstractTreeNode (GUIProofTreeModel tree, Node node) {
	this.tree = tree;
	this.noderef = new WeakReference<Node>(node);
    }

    public abstract TreeNode getChildAt(int childIndex);

    public abstract int getChildCount();

    public abstract TreeNode getParent();

    public abstract boolean isLeaf();

    public abstract void flushCache();

    public int getIndex(TreeNode node) {
	for ( int i=0; i<getChildCount(); i++ ) {
	    if ( getChildAt(i).equals(node) ) {
		return i;
	    }
	}
	return -1;
    }

    public boolean getAllowsChildren() {
	return ! isLeaf();
    }

    public Enumeration<TreeNode> children() {
	return new ChildEnumeration();
    }


    public TreeNode[] getPath() {
	LinkedList<TreeNode> path = new LinkedList<TreeNode>();
	TreeNode n = this;
	path.addFirst(n);
	while ( ( n = n.getParent() ) != null ) {
	    path.addFirst(n);
	}
	return path.toArray(new TreeNode[path.size()]);
    }

    protected TreeNode findBranch ( Node p_node ) {
	TreeNode res = getProofTreeModel ().findBranch ( p_node );
	if ( res != null )
	    return res;

	String label = p_node.getNodeInfo().getBranchLabel();

        if (p_node.root()) { 
            label = "Proof Tree";
        }
        if (label == null) {
            label = "Case " + (p_node.parent ().getChildNr ( p_node ) + 1);
            p_node.getNodeInfo().setBranchLabel(label);
        }

	return getProofTreeModel ().getBranchNode(p_node, label);
    }

    private class ChildEnumeration implements Enumeration<TreeNode> {
	int current = 0;

	public boolean hasMoreElements() {
	    return current < getChildCount();
	}

	public TreeNode nextElement() {
	    return getChildAt(current++);
	}
	
    }
    
    public Node getNode() {
        return noderef.get();
    }

    protected Node findChild (Node n) {
        if ( n.childrenCount () == 1 ) return n.child ( 0 );
        
        if ( !getProofTreeModel ().hideClosedSubtrees () )
            return null;
        
        Node nextN = null;
        for ( int i = 0; i != n.childrenCount (); ++i ) {
            if ( ! n.child ( i ).isClosed() ) {
                if ( nextN != null ) return null;
                nextN = n.child ( i );
            }
        }
    
        return nextN;
    }
}