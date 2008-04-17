// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.RuleAppListener;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.EnsuresPostPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.PreservesInvPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.RespectsModifiesPO;
import de.uka.ilkd.key.rule.IteratorOfRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SetAsListOfRuleApp;
import de.uka.ilkd.key.rule.SetOfRuleApp;

public class DefaultProofCorrectnessMgt implements ProofCorrectnessMgt {

    private final Proof proof;
    private final SpecificationRepository specRepos;
    private final DefaultMgtProofListener proofListener 
	= new DefaultMgtProofListener();
    private final DefaultMgtProofTreeListener proofTreeListener
	= new DefaultMgtProofTreeListener();
    
    private KeYMediator mediator;
    private SetOfRuleApp cachedRuleApps = SetAsListOfRuleApp.EMPTY_SET;
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
    
    private boolean atLeastOneClosed(SetOfProof proofs) {
        IteratorOfProof it = proofs.iterator();
        while(it.hasNext()) {
            Proof proof = it.next();
            proof.mgt().updateProofStatus();
            if(proof.mgt().getStatus().getProofClosed()) {
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
        SetOfProof proofs = specRepos.getProofs(pm);
        SetOfProof newProofs = proofs;
        while(newProofs.size() > 0) {
            IteratorOfProof it = newProofs.iterator();
            newProofs = SetAsListOfProof.EMPTY_SET;
            
            while(it.hasNext()) {
                Proof proof = it.next();
                IteratorOfRuleApp cachedRuleAppsIt 
                    = proof.mgt().getNonAxiomApps().iterator();
                while(cachedRuleAppsIt.hasNext()) {
                    RuleApp ruleApp = cachedRuleAppsIt.next();
                    RuleJustification ruleJusti = getJustification(ruleApp);
                    if(ruleJusti instanceof RuleJustificationBySpec) {
                        ContractWithInvs cwi 
                            = ((RuleJustificationBySpec) ruleJusti).getSpec();
                        SetOfProof proofsForPm 
                            = specRepos.getProofs(cwi.contract
                                                     .getProgramMethod());
                        newProofs = newProofs.union(proofsForPm);
                        proofs = proofs.union(proofsForPm);
                    }   
                }
            }
        }
        
        //is one of those proofs about the operation under verification? 
        IteratorOfProof it = proofs.iterator();
        while(it.hasNext()) {
            ProgramMethod pm2 = specRepos.getOperationForProof(it.next());
            if(pm2.equals(pmUnderVerification)) {
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
        IteratorOfRuleApp cachedRuleAppsIt = cachedRuleApps.iterator();
        while(cachedRuleAppsIt.hasNext()) {
            RuleApp ruleApp = cachedRuleAppsIt.next();
            RuleJustification ruleJusti = getJustification(ruleApp);
            if(ruleJusti instanceof RuleJustificationBySpec) {
                ContractWithInvs cwi 
                    = ((RuleJustificationBySpec) ruleJusti).getSpec();
                InitConfig initConfig = proof.env().getInitConfig();
                ProofOblInput ensuresPostPO 
                    = new EnsuresPostPO(initConfig, 
                                        cwi.contract, 
                                        cwi.assumedInvs);
                SetOfProof ensuresPostProofs 
                    = specRepos.getProofs(ensuresPostPO);
                ProofOblInput preservesInvPO
                    = new PreservesInvPO(initConfig, 
                                         cwi.contract.getProgramMethod(), 
                                         cwi.assumedInvs, 
                                         cwi.ensuredInvs);
                SetOfProof preservesInvProofs 
                    = specRepos.getProofs(preservesInvPO);
                ProofOblInput respectsModifiesPO
                    = new RespectsModifiesPO(initConfig, 
                                             cwi.contract, 
                                             cwi.assumedInvs);
                SetOfProof respectsModifiesProofs
                    = specRepos.getProofs(respectsModifiesPO);
                
                if(!(atLeastOneClosed(ensuresPostProofs)
                     && atLeastOneClosed(preservesInvProofs)
                     && atLeastOneClosed(respectsModifiesProofs))) {
                    proofStatus = ProofStatus.CLOSED_BUT_LEMMAS_LEFT;
                    return;
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

    
    public SetOfRuleApp getNonAxiomApps() {
	return cachedRuleApps;
    }

    
    public void setMediator ( KeYMediator p_mediator ) {
	if ( mediator != null )
	    mediator.removeRuleAppListener ( proofListener );

	mediator = p_mediator;

	if ( mediator != null )
	    mediator.addRuleAppListener ( proofListener );
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
