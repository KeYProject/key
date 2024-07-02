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

package de.uka.ilkd.key.proof.mgt;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;


/** Captures a node in the TaskTree which contains exactly one
 * proof. Such a node is the only one with a one to one mapping
 * between TaskTreeNode and Proof. It may be a sub task of a more
 * complex task such as ProofListTask.*/
public class BasicTask extends DefaultMutableTreeNode implements TaskTreeNode{

    /**
     * 
     */
    private static final long serialVersionUID = -6490453248054760812L;
    private ProofAggregate proof;

    /** creates a task with a single proof. The given proof list must
     * contain exactly one proof.*/
    public BasicTask(ProofAggregate pl) {
	super(pl);
	proof=pl;
    }

    public String shortDescr() {
	return proof().name().toString();
    }

    public String toString() {
	return shortDescr();
    }

    public ProofEnvironment getProofEnv() {
	return proof().getEnv();
    }

    /* returns the single proof of this task */
    public Proof proof() {
	return proof.getFirstProof();
    }

    /** returns all proofs attached to this basic task*/
    public Proof[] allProofs() {
	return new Proof[]{proof()};
    }

    /** inserts a node given the task tree model and a parent node */
    public void insertNode(TaskTreeModel model, MutableTreeNode parentNode) {
	model.insertNodeInto(this, parentNode, model.getChildCount(parentNode));
    }

    /** asks the proof management component of the associated proofs
     * for the status of the associated proof .
     */
    public ProofStatus getStatus() {
	return proof().mgt().getStatus();
    }
    

    /** returns the upper most task this basic task belongs to.*/
    public TaskTreeNode getRootTask() {
	TaskTreeNode tn = this;
	while (!(tn.getParent() instanceof EnvNode)) {
	    tn=(TaskTreeNode) tn.getParent();
	}
	return tn;
    }

    /** removes the associated proof from their environment*/
    public void decoupleFromEnv() {
       getProofEnv().removeProofList(proof);
    }

    @Override
    public TaskTreeNode[] getChildren() {
        return NO_CHILDREN;
    }
}