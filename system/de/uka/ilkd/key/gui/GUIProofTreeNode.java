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
/** this class implements a TreeModel that can be displayed using the
 * JTree class framework 
 */
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;

class GUIProofTreeNode extends GUIAbstractTreeNode 
                       implements TreeNode {

    private Node node;
    
    public GUIProofTreeNode(GUIProofTreeModel tree, Node node) {
	super ( tree );
	this.node = node;
    }


    public TreeNode getChildAt(int childIndex) {
	return null;
    }

    public int getChildCount() {
	return 0;
    }

    public TreeNode getParent() {
	Node n = node;
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
	return node;
    }

    public String toString() {
	// changed to serial:name for searching
	// the proof tree in ProofTreeView.java
	return node.serialNr()+":"+node.name();
    }
    
}
