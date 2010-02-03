// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

/** Encapsulates information describing changes to a proof tree, and
 * used to notify proof tree listeners of the change. This event is
 * used to encapsulate lost information after a node has been
 * removed, e.g. the parent of the removed node and the node itself.
 */

public class ProofTreeRemovedNodeEvent extends ProofTreeEvent {

    private Node removedNode;
    
    /** Create ProofTreeRemovedNodeEvent if a node of the proof has
     * been  removed
     * @param source the Proof where the event is happened
     * @param node the Node that was the parent of the removed node
     * @param removedNode the Node that has been removed
     */
    public ProofTreeRemovedNodeEvent(Proof source,
			  Node  node,
			  Node removedNode) {
	super(source, node);
	this.removedNode = removedNode;	
    }


    public Node getRemovedNode() {
	return removedNode;
    }
}

