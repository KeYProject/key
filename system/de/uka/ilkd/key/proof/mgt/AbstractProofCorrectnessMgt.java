package de.uka.ilkd.key.proof.mgt;

import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.RuleAppListener;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.RuleApp;

public abstract class AbstractProofCorrectnessMgt implements ProofCorrectnessMgt {

    protected final Proof proof;
    protected final SpecificationRepository specRepos;
    private final DefaultMgtProofListener proofListener = new DefaultMgtProofListener();
    protected final DefaultMgtProofTreeListener proofTreeListener = new DefaultMgtProofTreeListener();
    private KeYMediator mediator;
    protected ImmutableSet<RuleApp> cachedRuleApps = DefaultImmutableSet.<RuleApp>nil();
    protected ProofStatus proofStatus = null;

    public AbstractProofCorrectnessMgt(Proof p) {
	this.proof = p;
        this.specRepos = p.getServices().getSpecificationRepository();	
        proof.addProofTreeListener(proofTreeListener);

    }

    protected boolean atLeastOneClosed(ImmutableSet<Proof> proofs) {
        for (Proof proof1 : proofs) {
            Proof proof = proof1;
            proof.mgt().updateProofStatus();
            if (proof.mgt().getStatus().getProofClosed()) {
                return true;
            }
        }
        return false;
    }

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

    public void setMediator(KeYMediator p_mediator) {
        if ( mediator != null )
            mediator.removeRuleAppListener ( proofListener );
    
        mediator = p_mediator;
    
        if ( mediator != null )
            mediator.addRuleAppListener ( proofListener );
    }

    public void removeProofListener() {
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

    class DefaultMgtProofListener implements RuleAppListener {
	public void ruleApplied(ProofEvent e) {
	    if (AbstractProofCorrectnessMgt.this.getProof()==e.getSource()) {
                //%% actually I only want to listen to events of one proof
		AbstractProofCorrectnessMgt.this.ruleApplied
		    (e.getRuleAppInfo().getRuleApp());
	    }
	}
    }
    
    class DefaultMgtProofTreeListener extends ProofTreeAdapter {
	public void proofClosed(ProofTreeEvent e) {	    
	    ProofEnvironment pEnv = proof.env();
	    pEnv.updateProofStatus();
	}
    }
}
