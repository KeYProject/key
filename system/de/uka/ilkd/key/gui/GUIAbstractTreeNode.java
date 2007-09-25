// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui;


import java.util.Enumeration;
import java.util.LinkedList;

import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.ConstraintTableModel;
import de.uka.ilkd.key.proof.Node;


public abstract class GUIAbstractTreeNode implements TreeNode {

    private GUIProofTreeModel tree;
    
    protected GUIProofTreeModel getProofTreeModel () {
	return tree;
    }

    public GUIAbstractTreeNode ( GUIProofTreeModel tree ) {
	this.tree = tree;
    }

    public abstract TreeNode getChildAt(int childIndex);

    public abstract int getChildCount();

    public abstract TreeNode getParent();
    
    public abstract boolean isLeaf();


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

    public Enumeration children() {
	return new ChildEnumeration();
    }


    public Object[] getPath() {
	LinkedList path = new LinkedList();
	TreeNode n = this;
	//	System.out.println("1: "+n);
	path.addFirst(n);
	while ( ( n = n.getParent() ) != null ) {
	    //	    System.out.println("2: "+n+ "    "+path);
	    path.addFirst(n);
	}
	return path.toArray();
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

    private class ChildEnumeration implements Enumeration {
	int current = 0;

	public boolean hasMoreElements() {
	    return current < getChildCount();
	}

	public Object nextElement() {
	    return getChildAt(current++);
	}
	
    }
    
    public abstract Node getNode();

    protected Node findChild (Node n) {
        if ( n.childrenCount () == 1 ) return n.child ( 0 );
        
        if ( !getProofTreeModel ().hideClosedSubtrees () )
            return null;
        
        final ConstraintTableModel userConstraint = n.proof ()
            .getUserConstraint ();
    
        Node nextN = null;
        for ( int i = 0; i != n.childrenCount (); ++i ) {
            if ( !userConstraint.displayClosed ( n.child ( i ) ) ) {
                if ( nextN != null ) return null;
                nextN = n.child ( i );
            }
        }
    
        return nextN;
    }    
}

