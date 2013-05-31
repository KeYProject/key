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

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;

public class ProofAggregateTask extends DefaultMutableTreeNode 
    implements TaskTreeNode{

    /**
     * 
     */
    private static final long serialVersionUID = 2292876929382788414L;
    private TaskTreeNode[] proofs;
    private ProofAggregate proofList;
    private String descr;

    public ProofAggregateTask(ProofAggregate ps) {
        super(ps);       
        proofs=new TaskTreeNode[ps.size()];
        for (int i=0; i<ps.size(); i++) {
            if (ps.getChildren()[i] instanceof SingleProof) {
                proofs[i] = new BasicTask(ps.getChildren()[i]);
            } else {
                proofs[i]=new ProofAggregateTask(ps.getChildren()[i]);
            }
        }
        proofList=ps;
        descr=ps.description();
    }
    
    public String shortDescr() {
        return descr;
    }
    
    public String toString() {
        return shortDescr();
    }
    
    public ProofEnvironment getProofEnv() {
        return proofs[0].proof().env();
    }
    
    public ProofAggregate getProofList() {
        return proofList;
    }
    
    public Proof proof() {
        return proofs[0].proof();
    }
    
    public Proof[] allProofs() {
        return getProofList().getProofs();
    }
    
    public void insertNode(TaskTreeModel model, MutableTreeNode parentNode) {
        model.insertNodeInto(this, parentNode, model.getChildCount(parentNode));
        for (TaskTreeNode proof : proofs) {
            proof.insertNode(model, this);
        }
    }
    
    public ProofStatus getStatus() {
        return proofList.getStatus();
    }
    
    public void decoupleFromEnv() {
        getProofEnv().removeProofList(proofList);
    }
}
