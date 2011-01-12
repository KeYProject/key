// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
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
import java.lang.ref.WeakReference;

import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;

class GUIProofTreeNode extends GUIAbstractTreeNode 
                       implements TreeNode {

    private WeakReference<Node> noderef;//made weak otherwise there are leaks in ExpansionState.map and ProofTreeView.delegateView.lastPathComponent 
    
    public GUIProofTreeNode(GUIProofTreeModel tree, Node node) {
	super ( tree );
	this.noderef = new WeakReference<Node>(node);
    }


    public TreeNode getChildAt(int childIndex) {
	return null;
    }

    public int getChildCount() {
	return 0;
    }

    public TreeNode getParent() {
	Node n = noderef.get();
	if(n==null)return null;
	while (n.parent()!=null
	       && findChild ( n.parent() ) != null ) {
	    n = n.parent();
	}
	return findBranch(n);
    }
    
    public boolean isLeaf() {
	return true;
    }

    public Node getNode() {
	return noderef.get();
    }

    public String toString() {
	// changed to serial:name for searching
	// the proof tree in ProofTreeView.java
        Node n =noderef.get();
        if(n!=null){
	return n.serialNr()+":"+n.name();
        }else{
            return "Invalid WeakReference";
        }
    }
    
}
