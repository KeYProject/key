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
/** this class implements a TreeModel that can be displayed using the
 * JTree class framework 
 */

import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.OneStepSimplifier.Protocol;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;

class GUIProofTreeNode extends GUIAbstractTreeNode {

    private GUIAbstractTreeNode[] children;

    public GUIProofTreeNode(GUIProofTreeModel tree, Node node) {
	super(tree, node);
    }

    public TreeNode getChildAt(int childIndex) {
        ensureChildrenArray();
	return children[childIndex];
    }

    public int getChildCount() {
        ensureChildrenArray();
	return children.length;
    }

    public TreeNode getParent() {
	Node n = getNode();
	if(n==null)return null;
	while (n.parent()!=null
	       && findChild ( n.parent() ) != null ) {
	    n = n.parent();
	}
	return findBranch(n);
    }

    public boolean isLeaf() {
	return getChildCount() == 0;
    }

    public String toString() {
	// changed to serial:name for searching
        // the proof tree in ProofTreeView.java
        Node n = getNode();
        if (n != null) {
            return n.serialNr() + ":" + n.name();
        } else {
            return "Invalid WeakReference";
        }
    }

    /**
     * Ensure that the children array is valid.
     * 
     * Nodes may have children if they represent a One step simplification.
     * If so, the array of children is read from the rule app object
     */
    private void ensureChildrenArray() {
        if(children == null) {
            Node node = getNode();
            if(node != null && node.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp) {
                Protocol protocol = ((OneStepSimplifierRuleApp)node.getAppliedRuleApp()).getProtocol();
                if(protocol != null) {
                    children = new GUIAbstractTreeNode[protocol.size()];
                    for (int i = 0; i < children.length; i++) {
                        children[i] = new GUIOneStepChildTreeNode(getProofTreeModel(), 
                                this, protocol.get(i));
                    }
                    return;
                }
            }

            // otherwise
            children = new GUIAbstractTreeNode[0];
        }
    }
    
    @Override 
    public void flushCache() {
        children = null;
    }
}
