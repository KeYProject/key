// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.mgt;

import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.RuleAppListener;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.OperationContract;

public final class DefaultProofCorrectnessMgt implements ProofCorrectnessMgt {

    private final Proof proof;
    private final SpecificationRepository specRepos;
    private final DefaultMgtProofListener proofListener 
	= new DefaultMgtProofListener();
    private final DefaultMgtProofTreeListener proofTreeListener
	= new DefaultMgtProofTreeListener();
    
    private KeYMediator mediator;
    private ImmutableSet<RuleApp> cachedRuleApps 
    	= DefaultImmutableSet.<RuleApp>nil();
    private ProofStatus proofStatus = null;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public DefaultProofCorrectnessMgt(Proof p) {
	this.proof = p;
        this.specRepos = p.getServices().getSpecificationRepository();
	proof.addProofTreeListener(proofTreeListener);
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private boolean atLeastOneClosed(ImmutableSet<Proof> proofs) {
	for(Proof p : proofs) {
            p.mgt().updateProofStatus();
            if(p.mgt().getStatus().getProofClosed()) {
                return true;
            }
        }
        return false;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    @Override
    public RuleJustification getJustification(RuleApp r) {
	return proof.env()
	            .getJustifInfo()
	            .getJustification(r, proof.getServices());
    }

    
    /**
     * Tells whether a contract for the passed operation may be applied 
     * in the passed goal without creating circular dependencies.
     */
    @Override    
    public boolean contractApplicableFor(ProgramMethod pm, Goal g) {
        //get the method which is being verified in the passed goal
        final ProgramMethod pmUnderVerification 
            = specRepos.getOperationForProof(g.proof());
        if(pmUnderVerification == null) {
            return true;
        }
        
        //collect all proofs on which the specification of the 
        //passed method may depend
        ImmutableSet<Proof> proofs = specRepos.getProofs(pm);
        ImmutableSet<Proof> newProofs = proofs;
        while(newProofs.size() > 0) {
            final Iterator<Proof> it = newProofs.iterator();
            newProofs = DefaultImmutableSet.<Proof>nil();
            
            while(it.hasNext()) {
                final Proof p = it.next();
                for(OperationContract contract : p.mgt().getUsedContracts()) {
                    ImmutableSet<Proof> proofsForPm 
                    	= specRepos.getProofs(contract.getProgramMethod());
                    newProofs = newProofs.union(proofsForPm);
                    proofs = proofs.union(proofsForPm);                    
                }
            }
        }
        
        //is one of those proofs about the operation under verification? 
        for(Proof p : proofs) {
            final ProgramMethod pm2 = specRepos.getOperationForProof(p);
            if(pm2.equals(pmUnderVerification)) {
                return false;
            }
        }
        
        return true;
    }


    @Override    
    public void updateProofStatus() {
        //proof open?
        if(proof.openGoals().size() > 0) {
            proofStatus = ProofStatus.OPEN;
            return;
        }
	
        //used, but yet unproven specifications?        
        for(OperationContract contract : getUsedContracts()) { 
            InitConfig initConfig = proof.env().getInitConfig();
            ProofOblInput contractPO = new ContractPO(initConfig, contract);
            ImmutableSet<Proof> proofs = specRepos.getProofs(contractPO);
            if(!(atLeastOneClosed(proofs))) {
        	proofStatus = ProofStatus.CLOSED_BUT_LEMMAS_LEFT;
        	return;
            }
        }
        
        //no -> proof is closed
        proofStatus = ProofStatus.CLOSED;
    }

    
    @Override    
    public void ruleApplied(RuleApp r) {
	RuleJustification rj = getJustification(r);
	if(rj==null) {
	    System.err.println("No justification found for rule " 
		               + r.rule().name());
	    return;
	}
	if(!rj.isAxiomJustification()) {
            cachedRuleApps = cachedRuleApps.add(r);
	}
    }

    
    @Override    
    public void ruleUnApplied(RuleApp r) {
        int oldSize = cachedRuleApps.size();
        cachedRuleApps = cachedRuleApps.remove(r);
	if(oldSize != cachedRuleApps.size()) {
	    updateProofStatus();
	}
    }

    
    @Override    
    public ImmutableSet<RuleApp> getNonAxiomApps() {
	return cachedRuleApps;
    }

    
    @Override
    public ImmutableSet<OperationContract> getUsedContracts() {
	ImmutableSet<OperationContract> result 
		= DefaultImmutableSet.<OperationContract>nil();
	for(RuleApp ruleApp : cachedRuleApps) {
            RuleJustification ruleJusti = getJustification(ruleApp);
            if(ruleJusti instanceof RuleJustificationBySpec) {
        	OperationContract contract
                    = ((RuleJustificationBySpec) ruleJusti).getSpec();
        	ImmutableSet<OperationContract> atomicContracts
        		= specRepos.splitContract(contract);
        	assert atomicContracts != null;
        	atomicContracts 
        		= specRepos.getInheritedContracts(atomicContracts); 
        	result = result.union(atomicContracts);
            }
        }
	return result;
    }

    
    @Override    
    public void setMediator(KeYMediator p_mediator) {
	if(mediator != null) {
	    mediator.removeRuleAppListener(proofListener);
	}

	mediator = p_mediator;

	if(mediator != null) {
	    mediator.addRuleAppListener(proofListener);
	}
    }
    
    
    @Override    
    public void removeProofListener(){
        mediator.removeRuleAppListener(proofListener);
    }

    
    @Override
    public boolean proofSimilarTo(Proof p) {
	return p.name().equals(proof.name()); //%%%
    }

    
    @Override
    public ProofStatus getStatus() {
	if(proofStatus == null) updateProofStatus();
	return proofStatus;
    }
    
    
    @Override
    public void finalize() {
        if(mediator != null) {
            mediator.removeRuleAppListener(proofListener);
        }
    }

    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------
    
    private class DefaultMgtProofListener implements RuleAppListener {
	public void ruleApplied(ProofEvent e) {
	    if(DefaultProofCorrectnessMgt.this.proof == e.getSource()) {
                //%% actually I only want to listen to events of one proof
		DefaultProofCorrectnessMgt.this.ruleApplied
		    (e.getRuleAppInfo().getRuleApp());
	    }
	}
    }

    
    private class DefaultMgtProofTreeListener extends ProofTreeAdapter {
	public void proofClosed(ProofTreeEvent e) {	    
	    ProofEnvironment pEnv = proof.env();
	    pEnv.updateProofStatus();
	}
    }
}
