package de.uka.ilkd.key.gui.macros;

import java.util.LinkedList;
import java.util.List;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.utilities.KeyStrokeManager;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public class TestGenMacro implements ProofMacro {

	@Override
	public String getName() {

		return "TestGen";
	}

	@Override
	public String getDescription() {

		return "Generate test-cases for open goals";
	}

	@Override
	public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {

		return true;
	}
	
	/*
     * returns true if term is modality or update application
     */
    private static boolean hasModality(Term term) {
        if(term.op() instanceof Modality) {
            return true;
        }
        
        if(term.op() instanceof UpdateApplication){
        	return true;
        }

        return false;
    }
    
    private void findModalities(PosInOccurrence pio, List<PosInOccurrence> toRemove){
    	
    	if(pio == null){
    		return;
    	}
    	
    	if(hasModality(pio.constrainedFormula().formula())){
    		toRemove.add(pio);
    	}
    	
    	int length = pio.constrainedFormula().formula().subs().size();
    	
    	for(int i = 0; i< length; ++i){
    		findModalities(pio.down(i), toRemove);
    	}
    	
    	
    }

	@Override
	public void applyTo(KeYMediator mediator, PosInOccurrence posInOcc,
			ProverTaskListener listener) throws InterruptedException {

		final Proof proof = mediator.getInteractiveProver().getProof();
		Node invokedNode = mediator.getSelectedNode();
		
        ImmutableList<Goal> enabledGoals = proof.getSubtreeEnabledGoals(invokedNode);
        
        List<PosInOccurrence> toRemove = new LinkedList<PosInOccurrence>();
        findModalities(posInOcc, toRemove);
        
        
        for(Goal g : enabledGoals){
        	
        	Node node = g.node();
        	Sequent seq = node.sequent(); 
        	
        	
        	
        	for(PosInOccurrence pio : toRemove){
        		seq.removeFormula(pio);
        	}   	
        	
        }


	}

	@Override
	public KeyStroke getKeyStroke() {

		return KeyStrokeManager.get(this);
	}

}
