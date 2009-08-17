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

import java.util.Map;
import java.util.WeakHashMap;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TacletFilter;
import de.uka.ilkd.key.proof.TacletIndex;


public final class OneStepSimplifier implements BuiltInRule {
    
    public static final OneStepSimplifier INSTANCE 
                                            = new OneStepSimplifier();
    
    private static final Name NAME = new Name("One Step Simplification");
    
    private static final ImmutableList<String> ruleSets 
    	= ImmutableSLList.<String>nil().append("concrete")
    	                           .append("simplify_literals")
    	                           .append("simplify");
  
    private final Map<ConstrainedFormula, Instantiation> cache 
    		= new WeakHashMap<ConstrainedFormula, Instantiation>();
    
    private Proof lastProof;
    private ImmutableSet<NoPosTacletApp> appsTakenOver;
    private TacletIndex[] indices;
    
    

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private OneStepSimplifier() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private ImmutableSet<Taclet> tacletsForRuleSet(Goal goal, 
	    				  String ruleSetName,
	    				  ImmutableList<String> excludedRuleSetNames) {
	ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();
	ImmutableSet<NoPosTacletApp> allApps = goal.ruleAppIndex().tacletIndex()
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
	    for(RuleSet rs : app.taclet().getRuleSets()) {
		if(rs.name().toString().equals(ruleSetName)) {
		    accept = true;
		} else if(excludedRuleSetNames.contains(rs.name().toString())) {
		    accept = false;
		    break;
		}
	    }
	    
	    if(accept) {
		appsTakenOver = appsTakenOver.add(app);		
		goal.ruleAppIndex().removeNoPosTacletApp(app);
		result = result.add(app.taclet());
	    }
	}
	
	return result;
    }
    
    
    private void initIndices(Goal goal) {
	if(goal.proof() != lastProof) {
	    lastProof = goal.proof();	    
	    appsTakenOver = DefaultImmutableSet.<NoPosTacletApp>nil();;	    
	    indices = new TacletIndex[ruleSets.size()];
	    int i = 0;
	    ImmutableList<String> done = ImmutableSLList.<String>nil();
	    for(String ruleSet : ruleSets) {
		ImmutableSet<Taclet> taclets = tacletsForRuleSet(goal, 
						        ruleSet, 
						        done);
		indices[i++] = new TacletIndex(taclets);
		done = done.prepend(ruleSet);
	    }
	}
    }
    
    
    private void shutdownIndices() {
	if(lastProof != null) {
	    for(Goal g : lastProof.openGoals()) {
		for(NoPosTacletApp app : appsTakenOver) {
		    g.ruleAppIndex().addNoPosTacletApp(app);
		}
		g.getRuleAppManager().clearCache();
		g.ruleAppIndex().clearIndexes();		
	    }
	    lastProof = null;
	    appsTakenOver = null;
	    indices = null;
	}
    }
    
    
    private ConstrainedFormula simplifyPosOrSub(Services services,
	    		     	  	        PosInOccurrence pos,
	    		     	  	        int indexNr) {
	ImmutableList<NoPosTacletApp> apps 
		= indices[indexNr].getRewriteTaclet(pos, 
						    Constraint.BOTTOM, 
						    TacletFilter.TRUE, 
						    services, 
						    Constraint.BOTTOM);
	for(TacletApp app : apps) {	    
	    app = app.setPosInOccurrence(pos, services);
	    if(!app.complete()) {
		app = app.tryToInstantiate(services);
	    }
	    if(app != null) {
		RewriteTaclet taclet = (RewriteTaclet) app.rule();
		ConstrainedFormula result = taclet.getRewriteResult(services, 
								    app);
		return result;
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
    
    
    private Instantiation getInstantiation(Services services, 
	                                   ConstrainedFormula cf) {
	Instantiation result = cache.get(cf);
	
	if(result == null) {
	    ImmutableList<ConstrainedFormula> list 
	    	= ImmutableSLList.<ConstrainedFormula>nil().prepend(cf);
	    while(true) {
		ConstrainedFormula nextCF 
			= simplifyConstrainedFormula(services, 
					             list.head());
		if(nextCF != null && !list.contains(nextCF)) {
		    list = list.prepend(nextCF);
		} else {
		    break;
		}
	    }
	    
	    cache.put(list.head(), Instantiation.EMPTY_INSTANTIATION);
	    int i = 1;
	    for(ConstrainedFormula listEntry : list.tail()) {
		Instantiation inst = new Instantiation(list.head(), i++);
		cache.put(listEntry, inst);
	    }
	    
	    result = cache.get(cf);
	}
	
	assert result != null;
	return result;
    }
    
    

    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    @Override    
    public boolean isApplicable(Goal goal, 
                                PosInOccurrence pio, 
                                Constraint userConstraint) {
	//abort if not top level constrained formula
	if(pio == null || !pio.isTopLevel()) {
	    return false;
	}	
	
	//abort if switched off
	if(!ProofSettings.DEFAULT_SETTINGS
		         .getGeneralSettings()
		         .oneStepSimplification()) {
	    shutdownIndices();
	    return false;
	}
		
	//initialize if needed
	initIndices(goal);
	
	//get instantiation
	Services services = goal.proof().getServices();	
	Instantiation inst = getInstantiation(services, 
					      pio.constrainedFormula());

	//tell whether the instantiation is interesting
	return inst.getNumAppliedRules() > 0;
    }

    
    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
	final ImmutableList<Goal> result = goal.split(1);
	final Goal resultGoal = result.head();
	final PosInOccurrence pos = ruleApp.posInOccurrence();
	assert pos != null && pos.isTopLevel();
	
	Instantiation inst = getInstantiation(services, 
					      pos.constrainedFormula());
	assert inst.getNumAppliedRules() > 0;
	
	resultGoal.changeFormula(inst.getCf(), pos);
	goal.setBranchLabel(inst.getNumAppliedRules() + " rules");
	
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
	    assert numAppliedRules >= 0;
	    this.cf = cf;
	    this.numAppliedRules = numAppliedRules;
	}
	
	public ConstrainedFormula getCf() {
	    return cf;
	}
	
	public int getNumAppliedRules() {
	    return numAppliedRules;
	}
	
	public String toString() {
	    return cf + " (" + numAppliedRules + " rules)";
	}
    }
}
