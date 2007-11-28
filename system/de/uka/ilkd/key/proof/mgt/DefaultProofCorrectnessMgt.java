// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.proof.mgt;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.RuleAppListener;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.RuleApp;

public class DefaultProofCorrectnessMgt implements ProofCorrectnessMgt{

    private Proof proof;
    private Set cachedAppliedRules = new HashSet();
    private KeYMediator mediator;
    private DefaultMgtProofListener proofListener 
	= new DefaultMgtProofListener();
    private DefaultMgtProofTreeListener proofTreeListener
	= new DefaultMgtProofTreeListener();

    private ProofStatus proofStatus = null;

    private DepAnalysis lastAnalysisInfo;

    public DefaultProofCorrectnessMgt(Proof p) {
	this.proof=p;
	proof.addProofTreeListener(proofTreeListener);
    }

    public RuleJustification getJustification(RuleApp r) {
	return proof.env().getJustifInfo().getJustification(r, proof.getServices());
    }

    public boolean ruleApplicable(RuleApp r, Goal g) {
	final RuleJustification just = getJustification(r);
	if (just==null) {
	    System.err.println("Warning: No justification for rule " + 
			       r.rule().name()  +" found");
	    return true;
	}
        lastAnalysisInfo = just.dependsOn(proof);
	return !lastAnalysisInfo.depExists();
    }


    public String getLastAnalysisInfo() {
	return lastAnalysisInfo == null ? "" : lastAnalysisInfo.toString();
    }

    public void updateProofStatus() {
	boolean closed = false;
	boolean closedButLemmasLeft = false;
	boolean open = false;
	
	if (proof.openGoals().size() == 0){
	    // either closed or closedButLemmasLeft
	    Iterator cachedAppliedRulesIt = cachedAppliedRules.iterator();
	    
	    RuleApp rule = null;
	    RuleJustification ruleJusti = null;
	    List list = null;
	    Iterator listIterator = null;
	    ProofAggregate pl = null;
	    int size = 0;
	    Proof p = null;
	    
	    boolean allRulesClosed = true;
	    while (cachedAppliedRulesIt.hasNext()) {
		// every rule must be proven correct
		rule = (RuleApp) cachedAppliedRulesIt.next();
		ruleJusti = getJustification(rule);
		list = ruleJusti.getProofList();
		listIterator = list.iterator();
		boolean oneClosed = false;
		while (listIterator.hasNext()) {
		    // one of these must be closed
		    pl = (ProofAggregate) listIterator.next();
		    boolean allClosed = true;
		    Proof[] proofs = pl.getProofs();
		    size = proofs.length;
		    for (int i = 0; i < size; i++) {
			// all of these must be closed
			p = proofs[i];
			p.mgt().updateProofStatus();
			if (p.mgt().getStatus().getProofClosed()) {
			    // This proof is closed so it is possible
			    // that all proofs are closed.
			}
			else {
			    // There is a proof which is not closed,
			    // so not all proofs can be closed!
			    allClosed = false;
			}
		    }
		    if (allClosed) {
			// all proofs in the ProofList are closed, meaning
			// that this proof is closed
			oneClosed = true;
		    }
		    else {
			// Nothing to do here because this proof wasn't closed.
		    }
		}
		if (oneClosed) {
		    // This rule is closed so it is still possible all rules are
		    // closed and thus no need to change allRulesClosed here.
		}
		else {
		    allRulesClosed = false;
		}
	    }
	    if (allRulesClosed) {
		closed = true;
	    }
	    else {
		closedButLemmasLeft = true;
	    }
	}
	else {
	    open = true;
	}
	proofStatus = new ProofStatus(closed, closedButLemmasLeft, open);
    }

    private void cacheAppliedRule(RuleApp r) {
	cachedAppliedRules.add(r);
    }

    public void ruleApplied(RuleApp r) {
	RuleJustification rj = getJustification(r);
	if (rj==null) {
	    System.err.println("No justification found for rule " + r.rule().name());
	    return;
	}
	if (!rj.isAxiomJustification()) {
	    cacheAppliedRule(r);
	}
    }

    public void ruleUnApplied(RuleApp r) {
	boolean success = cachedAppliedRules.remove(r);
	if (success) {
	    updateProofStatus();
	}
    }

    public Iterator getAppliedNonAxioms() {
	return cachedAppliedRules.iterator();
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
    
    class DefaultMgtProofListener implements RuleAppListener {

	/** invoked when a rule has been applied */
	public void ruleApplied(ProofEvent e) {
	    if (DefaultProofCorrectnessMgt.this.getProof()==e.getSource()) {
                //%% actually I only want to listen to events of one proof
		DefaultProofCorrectnessMgt.this.ruleApplied
		    (e.getRuleAppInfo().getRuleApp());
	    }
	}
    }

    class DefaultMgtProofTreeListener extends ProofTreeAdapter {
	public void proofClosed(ProofTreeEvent e) {
	    ProofEnvironment pEnv = proof.env();
	    pEnv.updateProofStatus();
	}

	public void proofPruned(ProofTreeEvent e) {
	
	}

	public void proofGoalsAdded(ProofTreeEvent e) {
	    
	}

	public void proofStructureChanged(ProofTreeEvent e) {
	   
	}
    }
    

}
