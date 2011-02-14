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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TacletFilter;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.util.LRUCache;


public final class OneStepSimplifier implements BuiltInRule {
    
    public static final OneStepSimplifier INSTANCE 
                                            = new OneStepSimplifier();
    
    private static final Name NAME = new Name("One Step Simplification");
    private static final TermBuilder TB = TermBuilder.DF;
    
    private static final ImmutableList<String> ruleSets 
    	= ImmutableSLList.<String>nil().append("concrete")
    	                               .append("simplify_literals")
    	                               .append("elimQuantifier")
    	                               .append("simplify")
    	                               .append("simplify_enlarging");
    private static final boolean[] bottomUp 
    	= {false, false, false, false, true};
  
    private final Map<ConstrainedFormula, Instantiation> cache 
    		= new LRUCache<ConstrainedFormula, Instantiation>(1000);
   
    private Proof lastProof;
    private ImmutableSet<NoPosTacletApp> appsTakenOver;
    private TacletIndex[] indices;
    private Map<Term,Term> notSimplifiableCaches[];
    
    

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private OneStepSimplifier() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * Selects the taclets suitable for one step simplification out of the 
     * given rule set (where taclets that also belong to one of the "excluded"
     * rule sets are not considered). Removes these taclets from the goal's
     * taclet index, remembers them in the "appsTakenOver" field so they can
     * be restored later, and returns them.
     */
    private ImmutableSet<Taclet> tacletsForRuleSet(
	    			Goal goal, 
	    			String ruleSetName,
	    			ImmutableList<String> excludedRuleSetNames) {
	ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();
	ImmutableSet<NoPosTacletApp> allApps 
		= goal.ruleAppIndex().tacletIndex().allNoPosTacletApps();
	for(NoPosTacletApp app : allApps) {
	    if(!(app.taclet() instanceof RewriteTaclet)
	       || !app.taclet().hasReplaceWith()
	       || !app.taclet().ifSequent().isEmpty()	       
	       || app.taclet().goalTemplates().size() != 1
	       || !app.taclet().goalTemplates().head().sequent().isEmpty()
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
    
    
    /**
     * If the rule is applied to a different proof than last time, then clear
     * all caches and initialise the taclet indices.
     */
    private void initIndices(Goal goal) {
	if(goal.proof() != lastProof) {
	    shutdownIndices();
	    lastProof = goal.proof();	    
	    appsTakenOver = DefaultImmutableSet.<NoPosTacletApp>nil();;	    
	    indices = new TacletIndex[ruleSets.size()];
	    notSimplifiableCaches = new LRUCache[indices.length];
	    int i = 0;
	    ImmutableList<String> done = ImmutableSLList.<String>nil();
	    for(String ruleSet : ruleSets) {
		ImmutableSet<Taclet> taclets = tacletsForRuleSet(goal, 
						        	 ruleSet, 
						        	 done);
		indices[i] = new TacletIndex(taclets);
		notSimplifiableCaches[i] = new LRUCache<Term,Term>(10000);
		i++;
		done = done.prepend(ruleSet);
	    }
	}
    }
    
    
    /**
     * Deactivate one-step simplification: clear caches, restore taclets to
     * the goals' taclet indices.
     */
    private void shutdownIndices() {
	if(lastProof != null) {
	    for(Goal g : lastProof.openGoals()) {
		for(NoPosTacletApp app : appsTakenOver) {
		    g.ruleAppIndex().addNoPosTacletApp(app);
		}
		g.getRuleAppManager().clearCache();
		g.ruleAppIndex().clearIndexes();		
	    }
	    cache.clear();
	    lastProof = null;
	    appsTakenOver = null;
	    indices = null;
	    notSimplifiableCaches = null;
	}
    }
    
    
    /**
     * Helper for simplifyPosOrSub. Performs a single step of simplification 
     * locally at the given position using the given taclet index.
     */
    private ConstrainedFormula simplifyPos(Services services,
	  	        		   PosInOccurrence pos,
	  	        		   int indexNr) {
	final ImmutableList<NoPosTacletApp> apps 
		= indices[indexNr].getRewriteTaclet(pos, 
						    Constraint.BOTTOM, 
						    TacletFilter.TRUE, 
						    services, 
						    Constraint.BOTTOM);
	for(TacletApp app : apps) {
	    app = app.setPosInOccurrence(pos, services);
	    if(app == null) {
		continue;
	    } 
	    if(!app.complete()) {
		app = app.tryToInstantiate(services);
		if(app == null) {
		    continue;
		}
	    }
	    RewriteTaclet taclet = (RewriteTaclet) app.rule();		
	    ConstrainedFormula result = taclet.getRewriteResult(services, app);
	    return result;
	}
	return null;
    }
    
    
    /**
     * Helper for simplifyPosOrSub. Performs a single step of simplification 
     * recursively at a subterm of the given position using the given taclet 
     * index.
     */    
    private ConstrainedFormula simplifySub(Services services,
		   			   PosInOccurrence pos,
		   			   int indexNr) {
	for(int i = 0, n = pos.subTerm().arity(); i < n; i++) {
	    ConstrainedFormula result 
	    	= simplifyPosOrSub(services, pos.down(i), indexNr);
	    if(result != null) {
		return result;
	    }
	}	
	return null;
    }
    

    /**
     * Performs a single step of simplification at the given position or its 
     * subterms using the given taclet index.
     */
    private ConstrainedFormula simplifyPosOrSub(Services services,
	    		     	  	        PosInOccurrence pos,
	    		     	  	        int indexNr) {
	final Term term = pos.subTerm();
	if(notSimplifiableCaches[indexNr].get(term) != null) {
	    return null;
	}
	
	ConstrainedFormula result;
	if(bottomUp[indexNr]) {
	    result = simplifySub(services, pos, indexNr);
	    if(result == null) {
		result = simplifyPos(services, pos, indexNr);
	    }
	} else {
	    result = simplifyPos(services, pos, indexNr);
	    if(result == null) {
		result = simplifySub(services, pos, indexNr);
	    }
	}
	
	if(result == null) {
	    notSimplifiableCaches[indexNr].put(term, term);
	}
	
	return result;
    }
    
    
    /**
     * Helper for replaceKnown (handles recursion).
     */
    private Term replaceKnownHelper(Map<Term,PosInOccurrence> map, 
	                            Term in,
	                            /*out*/ List<PosInOccurrence> ifInsts) {
	final PosInOccurrence pos = map.get(in);
	if(pos != null) {
	    ifInsts.add(pos);
	    return pos.isInAntec() ? TB.tt() : TB.ff();
	} else if(in.op() instanceof Modality 
                  || in.op() instanceof UpdateApplication) {
	    return in;
	} else {
	    Term[] subs = new Term[in.arity()];
	    boolean changed = false;
	    for(int i = 0; i < subs.length; i++) {
		subs[i] = replaceKnownHelper(map, in.sub(i), ifInsts);
		if(subs[i] != in.sub(i)) {
		    changed = true;
		}
	    }
	    if(changed) {
		return TB.tf().createTerm(in.op(), 
					  subs, 
					  in.boundVars(), 
					  in.javaBlock());
	    } else {
		return in;
	    }
	}
    }
    
    
    /**
     * Simplifies the given constrained formula as far as possible using 
     * the replace-known rules (hardcoded here). The context formulas available 
     * for replace-known are passed in as "context". The positions of the
     * actually used context formulas are passed out as "ifInsts". 
     */
    private ConstrainedFormula replaceKnown(
	    				Services services, 
	                             	ConstrainedFormula cf,
	                             	Map<Term,PosInOccurrence> context,
	                             	/*out*/ List<PosInOccurrence> ifInsts) {
	if(context == null) {
	    return null;
	}
	final Term formula = cf.formula();
	final Term simplifiedFormula 
		= replaceKnownHelper(context, formula, ifInsts);
	if(simplifiedFormula.equals(formula)) {
	    return null; 
	} else {
	    return new ConstrainedFormula(simplifiedFormula);
	}
    }
    	   
    
    /**
     * Simplifies the passed constrained formula using a single taclet or 
     * arbitrarily many replace-known steps.
     */
    private ConstrainedFormula simplifyConstrainedFormula(
	    				Services services,
	    				ConstrainedFormula cf,
	    				Map<Term,PosInOccurrence> context,
	    				/*out*/ List<PosInOccurrence> ifInsts) {
	ConstrainedFormula result 
		= replaceKnown(services, cf, context, ifInsts);
	if(result != null) {
	    return result;
	}
	
	for(int i = 0; i < indices.length; i++) {
	    PosInOccurrence pos = new PosInOccurrence(cf,
	    		              		      PosInTerm.TOP_LEVEL,
	    		              		      true);
	    result = simplifyPosOrSub(services, pos, i);
	    if(result != null) {
		return result;
	    }
	}
	
	return null;
    }
    
    
    /**
     * Freshly computes the overall simplification result for the passed 
     * constrained formula. 
     */
    private Instantiation computeInstantiation(Services services,
	    				       ConstrainedFormula cf,
	    				       Sequent seq) {
	//try one simplification step without replace-known
	//give up if this does not work
	ConstrainedFormula simplifiedCf 
		= simplifyConstrainedFormula(services, cf, null, null);
	if(simplifiedCf == null || simplifiedCf.equals(cf)) {
	    return new Instantiation(cf, 
		                     0, 
		                     ImmutableSLList.<PosInOccurrence>nil());
	}
	
	//collect context formulas (potential if-insts for replace-known)
	final Map<Term,PosInOccurrence> context 
		= new HashMap<Term,PosInOccurrence>();
	for(ConstrainedFormula ante : seq.antecedent()) {
	    if(!ante.equals(cf) && ante.formula().op() != Junctor.TRUE) {
		context.put(
			ante.formula(), 
			new PosInOccurrence(ante, PosInTerm.TOP_LEVEL, true));
	    }
	}
	for(ConstrainedFormula succ : seq.succedent()) {
	    if(!succ.equals(cf) && succ.formula().op() != Junctor.FALSE) {
		context.put(
			succ.formula(), 
			new PosInOccurrence(succ, PosInTerm.TOP_LEVEL, false));
	    }
	}
	final List<PosInOccurrence> ifInsts 
		= new ArrayList<PosInOccurrence>(seq.size());
	
	//simplify as long as possible
	ImmutableList<ConstrainedFormula> list 
		= ImmutableSLList.<ConstrainedFormula>nil()
				 .prepend(simplifiedCf);
	while(true) {
	    simplifiedCf = simplifyConstrainedFormula(services, 
		    				      simplifiedCf,
		    				      context,
		    				      ifInsts);
	    if(simplifiedCf != null && !list.contains(simplifiedCf)) {
		list = list.prepend(simplifiedCf);
	    } else {
		break;
	    }
	}

	//return
	PosInOccurrence[] ifInstsArr = ifInsts.toArray(new PosInOccurrence[0]);
	ImmutableList<PosInOccurrence> immutableIfInsts
		= ImmutableSLList.<PosInOccurrence>nil().append(ifInstsArr);
	return new Instantiation(list.head(), 
		                 list.size(),
		                 immutableIfInsts);	
    }
    
    
    /**
     * Determines the overall simplification result for the passed constrained
     * formula. Uses cache to (re)compute this result only when necessary.
     */
    private Instantiation getInstantiation(Services services, 
	                                   ConstrainedFormula cf,
	                                   Sequent seq) {
	Instantiation result = cache.get(cf);
	
	//check whether if-insts still available	
	if(result != null) {
	    for(PosInOccurrence pos : result.ifInsts) {
		if(pos.isInAntec()) { 
	            if(!seq.antecedent().contains(pos.constrainedFormula())) {
		    	result = null;
			break;
		    }
		} else if(!seq.succedent().contains(pos.constrainedFormula())) {
		    result = null;
		    break;
		}
	    }
	}
	
	//(re)compute if needed
	if(result == null) {
	    result = computeInstantiation(services, cf, seq);
	    cache.put(cf, result);
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
					      pio.constrainedFormula(),
					      goal.sequent());

	//tell whether the instantiation is interesting
	return inst.getNumAppliedRules() > 0;
    }

    
    @Override
    public ImmutableList<Goal> apply(Goal goal, 
	    			     Services services, 
	    			     RuleApp ruleApp) {
	final ImmutableList<Goal> result = goal.split(1);
	final Goal resultGoal = result.head();
	final PosInOccurrence pos = ruleApp.posInOccurrence();
	assert pos != null && pos.isTopLevel();
		
	//get instantiation
	final Instantiation inst = getInstantiation(services, 
					            pos.constrainedFormula(),
					            goal.sequent());
	
	//change goal, set if-insts
	resultGoal.changeFormula(inst.getCf(), pos);
	goal.setBranchLabel(inst.getNumAppliedRules() + " rules");
	((BuiltInRuleApp)ruleApp).setIfInsts(inst.getIfInsts());
	
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
	private final ConstrainedFormula cf;
	private final int numAppliedRules;
	private final ImmutableList<PosInOccurrence> ifInsts;
		
	public Instantiation(ConstrainedFormula cf, 
		             int numAppliedRules,
		             ImmutableList<PosInOccurrence> ifInsts) {
	    assert numAppliedRules >= 0;
	    this.cf = cf;
	    this.numAppliedRules = numAppliedRules;
	    this.ifInsts = ifInsts;
	}
	
	public ConstrainedFormula getCf() {
	    return cf;
	}
	
	public int getNumAppliedRules() {
	    return numAppliedRules;
	}
	
	public ImmutableList<PosInOccurrence> getIfInsts() {
	    return ifInsts;
	}
	
	public String toString() {
	    return cf + " (" + (numAppliedRules > 1 ? " rules)" : "rule)");
	}
    }
}
