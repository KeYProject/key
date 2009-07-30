// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import java.util.*;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.*;


public final class OneStepSimplifier implements BuiltInRule {
    
    public static final OneStepSimplifier INSTANCE 
                                            = new OneStepSimplifier();
    
    private static final Name NAME = new Name("One Step Simplification");
  
    private static final Map<ConstrainedFormula, Instantiation> cache 
    		= new WeakHashMap<ConstrainedFormula, Instantiation>();
    
    private TacletIndex[] indices;
    private Proof lastProof;
    
    

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private OneStepSimplifier() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private SetOfTaclet tacletsForRuleSet(Goal goal, 
	    				  String ruleSetName,
	    				  ListOfString excludedRuleSetNames) {
	SetOfTaclet result = SetAsListOfTaclet.EMPTY_SET;
	SetOfNoPosTacletApp allApps = goal.ruleAppIndex().tacletIndex()
	                                                 .allNoPosTacletApps();
	for(NoPosTacletApp app : allApps) {
	    if(!(app.taclet() instanceof RewriteTaclet)
	       || !app.taclet().hasReplaceWith()
	       || app.taclet().goalTemplates().size() != 1
	       || !app.taclet().ifSequent().isEmpty()
	       || ((RewriteTaclet)app.taclet()).getStateRestriction() 
	             != RewriteTaclet.NONE
	       || !goal.proof().mgt().getJustification(app)
	                             .isAxiomJustification()) {
	        continue;
	    }
	    
	    boolean accept = false;	    
	    for(RuleSet rs : (app.taclet()).getRuleSets()) {
		if(rs.name().toString().equals(ruleSetName)) {
		    accept = true;
		} else if(excludedRuleSetNames.contains(rs.name().toString())) {
		    accept = false;
		    break;
		}
	    }
	    
	    if(accept) {
		result = result.add(app.taclet());
	    }
	}
	
	return result;
    }
    
    
    private void initIndices(Goal goal) {
	if(goal.proof() != lastProof) {
	    indices = new TacletIndex[2];
	    indices[0] = new TacletIndex(tacletsForRuleSet(
		    		goal, 
		    		"concrete", 
		    		SLListOfString.EMPTY_LIST));
	    indices[1] = new TacletIndex(tacletsForRuleSet(
		    		goal, 
		    		"simplify", 
		    		SLListOfString.EMPTY_LIST.prepend("concrete")));
	    lastProof = goal.proof();
	}
    }
    
    
    private ConstrainedFormula simplifyPosOrSub(Services services,
	    		     	  	        PosInOccurrence pos,
	    		     	  	        int indexNr) {
	ListOfNoPosTacletApp apps 
		= indices[indexNr].getRewriteTaclet(pos, 
						    Constraint.BOTTOM, 
						    TacletFilter.TRUE, 
						    services, 
						    Constraint.BOTTOM);
	for(TacletApp app : apps) {	    
	    app = ((NoPosTacletApp)app).matchFind(pos, 
		                                  Constraint.BOTTOM, 
		                                  services, 
		                                  Constraint.BOTTOM);
	    if(app != null) {
		app = app.setPosInOccurrence(pos);
		if(!app.complete()) {
		    app = app.tryToInstantiate(services);
		}
		if(app != null) {
		    RewriteTaclet taclet = (RewriteTaclet) app.rule();
		    ConstrainedFormula result 
		    	= taclet.getRewriteResult(services, app);
		    return result;
		} 
	    }
	}
	
	Term term = pos.subTerm();
	for(int i = 0, n = term.arity(); i < n; i++) {
	    ConstrainedFormula result 
	    	= simplifyPosOrSub(services, pos.down(i), indexNr);
	    if(result != null) {
		return result;
	    }
	}
	
	return null;
    }
    	   
    
    private ConstrainedFormula simplifyConstrainedFormula(
	    				    Services services,
	    				    ConstrainedFormula cf) {
	for(int i = 0; i < indices.length; i++) {
	    PosInOccurrence pos = new PosInOccurrence(cf,
	    		              		      PosInTerm.TOP_LEVEL,
	    		              		      true);
	    ConstrainedFormula result = simplifyPosOrSub(services, pos, i);
	    if(result != null) {
		return result;
	    }
	}
	
	return null;
    }
    
    
    private void fillCacheForSequent(Services services, Sequent seq) {
	for(final ConstrainedFormula originalCf : seq) {
	    if(cache.containsKey(originalCf)) {
		continue;
	    }
	    
	    ConstrainedFormula currentCF = originalCf;
	    ConstrainedFormula simplifiedCF;
	    int numAppliedRules = 0;
	    do {
		simplifiedCF = simplifyConstrainedFormula(services, 
							  currentCF);
		if(simplifiedCF != null) {
		    currentCF = simplifiedCF;
		    numAppliedRules++;
		}
	    } while(simplifiedCF != null);
	    
	    if(currentCF != originalCf) {
		Instantiation inst = new Instantiation(currentCF, 
			                               numAppliedRules);
		cache.put(originalCf, inst);
		cache.put(currentCF, Instantiation.EMPTY_INSTANTIATION);
	    } else {
		cache.put(originalCf, Instantiation.EMPTY_INSTANTIATION);
	    }
	}	
    }
    
    

    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    @Override    
    public boolean isApplicable(Goal goal, 
                                PosInOccurrence pio, 
                                Constraint userConstraint) {
	//abort if switched off
	if(! ProofSettings.DEFAULT_SETTINGS
		          .getGeneralSettings()
		          .oneStepSimplification()) {
	    return false;
	}
	
	//initialize if needed
	initIndices(goal);
	
	//instantiate if needed
	Services services = goal.proof().getServices();	
	Sequent seq = goal.sequent();	
	fillCacheForSequent(services, seq);

	//tell whether one of the instantiations is interesting
	for(ConstrainedFormula cf : seq) {
	    Instantiation inst = cache.get(cf);
	    if(inst.getNumAppliedRules() > 0) {
		return true;
	    }
	}
	return false;
    }

    
    @Override
    public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {
	final ListOfGoal result = goal.split(1);
	final Goal resultGoal = result.head();
	
	int numAppliedRules = 0;
	for(ConstrainedFormula cf : goal.sequent().antecedent()) {
	    Instantiation inst = cache.get(cf);
	    if(inst.getNumAppliedRules() > 0) {
		numAppliedRules += inst.getNumAppliedRules();
		resultGoal.changeFormula(inst.getCf(), new PosInOccurrence(cf, PosInTerm.TOP_LEVEL, true));
	    }
	}
	for(ConstrainedFormula cf : goal.sequent().succedent()) {
	    Instantiation inst = cache.get(cf);
	    if(inst.getNumAppliedRules() > 0) {
		numAppliedRules += inst.getNumAppliedRules();
		resultGoal.changeFormula(inst.getCf(), new PosInOccurrence(cf, PosInTerm.TOP_LEVEL, false));
	    }
	}	
	
	goal.setBranchLabel(numAppliedRules + " rules");
	return result;
    }
    
    
    @Override
    public Name name() {
        return NAME;
    }


    @Override
    public String displayName() { 
        return NAME.toString();
    }
    
    
    @Override
    public String toString() {
        return displayName();
    }
    
    

    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------
    
    private static final class Instantiation {
	private static final Instantiation EMPTY_INSTANTIATION 
		= new Instantiation(null, 0);
	
	private final ConstrainedFormula cf;
	private final int numAppliedRules;
	
	public Instantiation(ConstrainedFormula cf, int numAppliedRules) {
	    this.cf = cf;
	    this.numAppliedRules = numAppliedRules;
	}
	
	public ConstrainedFormula getCf() {
	    return cf;
	}
	
	public int getNumAppliedRules() {
	    return numAppliedRules;
	}
    }
}
