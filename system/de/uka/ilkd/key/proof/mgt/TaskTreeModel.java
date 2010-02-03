// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import java.util.HashMap;
import java.util.Map;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;


public class TaskTreeModel extends DefaultTreeModel {

    private Map proofToTask = new HashMap();

    public TaskTreeModel() {
	super(new DefaultMutableTreeNode("Tasks"));
    }

    public void addTask(TaskTreeNode p) {	
	ProofEnvironment env = p.getProofEnv();
	int size = getChildCount(getRoot());
	for (int i=0; i<size; i++) {
	    MutableTreeNode envNode = (MutableTreeNode) getChild(getRoot(), i);
	    if (env==((EnvNode) envNode).getProofEnv()) {
		p.insertNode(this, envNode);
		updateProofToTask(p);
		return;
	    }
	} //env not present yet
	EnvNode envNode = new EnvNode(env);
	insertNodeInto(envNode, (MutableTreeNode) getRoot(), size);
	updateProofToTask(p);
	p.insertNode(this, envNode);
    }

    public void removeTask(TaskTreeNode p) {
	Proof[] allProofs = p.allProofs();
	for (int i=0; i<allProofs.length; i++) {
	    proofToTask.remove(allProofs[i]);
            Node.clearReuseCandidates(allProofs[i]); // yes, listeners...
	    p.decoupleFromEnv();
	}
	if (p.getParent().getChildCount()==1) { // remove env if p is single
            GlobalProofMgt.getInstance().removeEnv(p.getProofEnv());
	    p = (TaskTreeNode) p.getParent();
	}
	removeNodeFromParent(p);
	p.getProofEnv().updateProofStatus(); // this should be done by listeners
    }

    private void updateProofToTask(TaskTreeNode p) {
	Proof[] proofs = p.allProofs();
	for (int i=0; i<proofs.length; i++) {
	    proofToTask.put(proofs[i], p);
	}
    }

    public TaskTreeNode getTaskForProof(Proof p) {
	if (p==null) return null;
	return p.getBasicTask();
    }

    public TaskTreeNode addProof(ProofAggregate plist) {
 	TaskTreeNode bp;
	if (plist.size()==1) {
	    bp = new BasicTask(plist);
	} else {
	    bp = new ProofAggregateTask(plist);
	}
	addTask(bp);
	return bp;
    }



} 
