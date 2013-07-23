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


package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;


public class TaskTreeModel extends DefaultTreeModel {

    /**
     * 
     */
    private static final long serialVersionUID = -4168248377205879699L;
    private Map<Proof, TaskTreeNode> proofToTask = new LinkedHashMap<Proof, TaskTreeNode>();

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
	    p.decoupleFromEnv();
	}
	ProofEnvironment env = p.getProofEnv();
	if (p.getParent().getChildCount()==1) { // remove env if p is single
            GlobalProofMgt.getInstance().removeEnv(env);
            env = null;
	    p = (TaskTreeNode) p.getParent();
	}
	if (p.getParent() != null) { // Make sure that p has a parent, because otherwise throws removeNodeFromParent(p): java.lang.IllegalArgumentException: node does not have a parent.
	   removeNodeFromParent(p);
	}
	
	if(env != null) {
	    env.getProofs()
	       .iterator()
	       .next()
	       .getProofs()[0]
	       .mgt()
	       .updateProofStatus();
	}
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
