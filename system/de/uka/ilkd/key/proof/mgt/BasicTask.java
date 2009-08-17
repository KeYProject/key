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

import java.util.Iterator;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.RuleApp;


/** Captures a node in the TaskTree which contains exactly one
 * proof. Such a node is the only one with a one to one mapping
 * between TaskTreeNode and Proof. It may be a sub task of a more
 * complex task such as ProofListTask.*/
public class BasicTask extends DefaultMutableTreeNode implements TaskTreeNode{

    private ProofAggregate proof;

    /** creates a task with a single proof. The given proof list must
     * contain exactly one proof.*/
    public BasicTask(ProofAggregate pl) {
	super(pl);
	proof=pl;
	proof().setBasicTask(this);
    }

    public String shortDescr() {
	return proof().name().toString();
    }

    public String toString() {
	return shortDescr();
    }

    public ProofEnvironment getProofEnv() {
	return proof().env();
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
    
    /** returns a list of operation contracts (with associated class invariants)
     *  that were used in the associated proof.
     */
    public ImmutableSet<ContractWithInvs> getUsedSpecs() {
        ImmutableSet<ContractWithInvs> result = DefaultImmutableSet.<ContractWithInvs>nil();       
        Iterator<RuleApp> it = proof().mgt().getNonAxiomApps().iterator();
        while(it.hasNext()) {
            RuleApp r = (RuleApp) it.next();
	    RuleJustification rj = proof().mgt().getJustification(r);            
	    if(rj instanceof RuleJustificationBySpec) {
                ContractWithInvs spec = ((RuleJustificationBySpec)rj).getSpec();
                assert spec != null;
                result = result.add(spec);
            }
	}
        
        return result;
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
}
