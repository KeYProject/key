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

public class DefaultProofCorrectnessMgt implements ProofCorrectnessMgt {

    private final Proof proof;
    private final SpecificationRepository specRepos;
    private final DefaultMgtProofListener proofListener 
	= new DefaultMgtProofListener();
    private final DefaultMgtProofTreeListener proofTreeListener
	= new DefaultMgtProofTreeListener();
    
    private KeYMediator mediator;
    private ImmutableSet<RuleApp> cachedRuleApps = DefaultImmutableSet.<RuleApp>nil();
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
        for (Proof proof1 : proofs) {
            Proof proof = proof1;
            proof.mgt().updateProofStatus();
            if (proof.mgt().getStatus().getProofClosed()) {
                return true;
            }
        }
        return false;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public RuleJustification getJustification(RuleApp r) {
	return proof.env().getJustifInfo().getJustification(r, proof.getServices());
    }

    
    /**
     * Tells whether a contract for the passed operation may be applied 
     * in the passed goal without creating circular dependencies.
     */
    public boolean contractApplicableFor(ProgramMethod pm, Goal g) {
        //get the method which is being verified in the passed goal
        ProgramMethod pmUnderVerification 
            = specRepos.getOperationForProof(g.proof());
        if(pmUnderVerification == null) {
            return true;
        }
        
        //collect all proofs on which the specification of the 
        //passed operation may depend
        ImmutableSet<Proof> proofs = specRepos.getProofs(pm);
        ImmutableSet<Proof> newProofs = proofs;
        while(newProofs.size() > 0) {
            Iterator<Proof> it = newProofs.iterator();
            newProofs = DefaultImmutableSet.<Proof>nil();
            
            while(it.hasNext()) {
                Proof proof = it.next();
                for (RuleApp ruleApp1 : proof.mgt().getNonAxiomApps()) {
                    RuleApp ruleApp = ruleApp1;
                    RuleJustification ruleJusti = getJustification(ruleApp);
                    if (ruleJusti instanceof RuleJustificationBySpec) {
                        ContractWithInvs cwi
                                = ((RuleJustificationBySpec) ruleJusti).getSpec();
                        ImmutableSet<Proof> proofsForPm
                                = specRepos.getProofs(cwi.contract
                                .getProgramMethod());
                        newProofs = newProofs.union(proofsForPm);
                        proofs = proofs.union(proofsForPm);
                    }
                }
            }
        }
        
        //is one of those proofs about the operation under verification? 
        for (Proof proof1 : proofs) {
            ProgramMethod pm2 = specRepos.getOperationForProof(proof1);
            if (pm2.equals(pmUnderVerification)) {
                return false;
            }
        }
        
        return true;
    }

    
    public void updateProofStatus() {
        //proof open?
        if(proof.openGoals().size() > 0) {
            proofStatus = ProofStatus.OPEN;
            return;
        }
	
        //used, but yet unproven specifications?
        for (RuleApp cachedRuleApp : cachedRuleApps) {
            RuleApp ruleApp = cachedRuleApp;
            RuleJustification ruleJusti = getJustification(ruleApp);
            if (ruleJusti instanceof RuleJustificationBySpec) {
                ContractWithInvs cwi
                        = ((RuleJustificationBySpec) ruleJusti).getSpec();
                for (OperationContract atomicContract
                        : proof.getServices().getSpecificationRepository()
                        .splitContract(cwi.contract)) {

                    InitConfig initConfig = proof.env().getInitConfig();
                    ProofOblInput ensuresPostPO
                            = new EnsuresPostPO(initConfig,
                            atomicContract,
                            cwi.assumedInvs);
                    ImmutableSet<Proof> ensuresPostProofs
                            = specRepos.getProofs(ensuresPostPO);
                    ProofOblInput preservesInvPO
                            = new PreservesInvPO(initConfig,
                            atomicContract.getProgramMethod(),
                            cwi.assumedInvs,
                            cwi.ensuredInvs);
                    ImmutableSet<Proof> preservesInvProofs
                            = specRepos.getProofs(preservesInvPO);
                    ProofOblInput respectsModifiesPO
                            = new RespectsModifiesPO(initConfig,
                            atomicContract,
                            cwi.assumedInvs);
                    ImmutableSet<Proof> respectsModifiesProofs
                            = specRepos.getProofs(respectsModifiesPO);

                    if (!(atLeastOneClosed(ensuresPostProofs)
                            && atLeastOneClosed(preservesInvProofs)
                            && atLeastOneClosed(respectsModifiesProofs))) {
                        proofStatus = ProofStatus.CLOSED_BUT_LEMMAS_LEFT;
                        return;
                    }
                }
            }
        }
        
        //no -> proof is closed
        proofStatus = ProofStatus.CLOSED;
    }

    
    public void ruleApplied(RuleApp r) {
	RuleJustification rj = getJustification(r);
	if (rj==null) {
	    System.err.println("No justification found for rule " + r.rule().name());
	    return;
	}
	if (!rj.isAxiomJustification()) {
            cachedRuleApps = cachedRuleApps.add(r);
	}
    }

    
    public void ruleUnApplied(RuleApp r) {
        int oldSize = cachedRuleApps.size();
        cachedRuleApps = cachedRuleApps.remove(r);
	if(oldSize != cachedRuleApps.size()) {
	    updateProofStatus();
	}
    }

    
    public ImmutableSet<RuleApp> getNonAxiomApps() {
	return cachedRuleApps;
    }

    
    public void setMediator ( KeYMediator p_mediator ) {
	if ( mediator != null )
	    mediator.removeRuleAppListener ( proofListener );

	mediator = p_mediator;

	if ( mediator != null )
	    mediator.addRuleAppListener ( proofListener );
    }
    
    public void removeProofListener(){
        mediator.removeRuleAppListener(proofListener);
    }

    
    public Proof getProof() {
	return proof;
    }

    
    public boolean proofSimilarTo(Proof p) {
	return p.name().equals(getProof().name()); //%%%
    }

    
    public ProofStatus getStatus() {
	if (proofStatus == null) updateProofStatus();
	return proofStatus;
    }
    
    
    public void finalize() {
        if (mediator != null) {
            mediator.removeRuleAppListener(proofListener);
        }
    }

    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------
    
    private class DefaultMgtProofListener implements RuleAppListener {
	public void ruleApplied(ProofEvent e) {
	    if (DefaultProofCorrectnessMgt.this.getProof()==e.getSource()) {
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
