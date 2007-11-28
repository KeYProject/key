// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.prooftree;
/** this class implements a TreeModel that can be displayed using the
 * JTree class framework 
 */
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.ConstraintTableModel;
import de.uka.ilkd.key.proof.Node;

class GUIBranchNode extends GUIAbstractTreeNode 
                    implements TreeNode {

    private Node   subTree;
    private Object label;
    
    public GUIBranchNode(GUIProofTreeModel tree,
			 Node subTree,
			 Object   label) {
	super ( tree );
	this.subTree = subTree;
	this.label = label;
    }

    
    private TreeNode[] childrenCache = null;
    
    private void createChildrenCache() {
        childrenCache = new TreeNode [getChildCountHelp()];
    }
    
    public TreeNode getChildAt(int childIndex) {
        fillChildrenCache();
        return childrenCache[childIndex];
        
        /*
	int count = 0;
	Node n = subTree;
	while ( childIndex != count 
	        && n.childrenCount() == 1 ) {
	    count++;
	    n = n.child(0);
	}
	if ( childIndex == count ) {
	    return getProofTreeModel ().getProofTreeNode(n);
	} else {
	    return findBranch ( n.child(childIndex-count-1) );
	}
   */
    }

    private void fillChildrenCache() {
        if ( childrenCache == null ) createChildrenCache ();
        if ( childrenCache.length == 0 || childrenCache[0] != null ) return;
            
        int count = 0;
        Node n = subTree;
        while ( true ) {
            childrenCache[count] = getProofTreeModel ().getProofTreeNode(n);
            count++;
            final Node nextN = findChild ( n );
            if ( nextN == null ) break;
            n = nextN;
        }
            
        final ConstraintTableModel userConstraint = n.proof ()
            .getUserConstraint ();

        for (int i = 0; i != n.childrenCount(); ++i) {
            if (!getProofTreeModel().hideClosedSubtrees() || !userConstraint
                .displayClosed ( n.child ( i ) ) ) {
                childrenCache[count] = findBranch ( n.child(i) );
                count++;
            }
        }
    }

    public void flushCache() {
        childrenCache = null;
    }
    
    public int getChildCount() {
        if ( childrenCache == null ) createChildrenCache ();
        return childrenCache.length;
    }

    private int getChildCountHelp() {
        int count = 0;
        Node n = subTree;
        while ( true ) {
            count++;
            final Node nextN = findChild ( n );
            if ( nextN == null ) break;
            n = nextN;
        }
        final ConstraintTableModel userConstraint = n.proof ()
            .getUserConstraint ();
        for (int i = 0; i != n.childrenCount(); ++i) {
            if (!getProofTreeModel().hideClosedSubtrees() || !userConstraint
                .displayClosed ( n.child ( i ) ) ) {
                count++;
            }
        }
        return count;
    }

    
    public TreeNode getParent() {
	Node n = subTree.parent();
	if ( n==null ) {
	    return null;
	} else {
	    while (n.parent()!=null
		   && findChild ( n.parent() ) != null ) {
		n = n.parent();
	    }
	    return findBranch(n);
	}
    }

    public Node getNode() {
	return subTree;
    }

    // signalled by GUIProofTreeModel when the user has altered the value
    public void setLabel(String s) {
	subTree.getNodeInfo().setBranchLabel(s);
    }

    public boolean isLeaf() {
	return false;
    }

    public String toString() {
	String res = subTree.getNodeInfo().getBranchLabel();
	if ( res == null )
	    return label.toString();
	return res;
    }


}
