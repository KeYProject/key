// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
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


public final class OneStepSimplifier implements BuiltInRule, 	
						KeYSelectionListener {
    
    public static final OneStepSimplifier INSTANCE 
                                            = new OneStepSimplifier();
    
    private static final Name NAME = new Name("One Step Simplification");
    private static final TermBuilder TB = TermBuilder.DF;
    
    private static final ImmutableList<String> ruleSets 
    	= ImmutableSLList.<String>nil().append("concrete")    	                            
    	                               .append("update_elim")
                                       .append("update_apply_on_update")
                                       .append("update_apply")
                                       .append("update_join")
    	                               .append("elimQuantifier");

    private static final boolean[] bottomUp 
        = {false, false, true, true, true, false};
    private final Map<SequentFormula,Boolean> applicabilityCache 
    		= new LRUCache<SequentFormula,Boolean>(100);
   
    private Proof lastProof;
    private ImmutableSet<NoPosTacletApp> appsTakenOver;
    private TacletIndex[] indices;
    private Map<Term,Term> notSimplifiableCaches[];
    private boolean active;
    
    

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
	    			Proof proof, 
	    			String ruleSetName,
	    			ImmutableList<String> excludedRuleSetNames) {
	assert !proof.openGoals().isEmpty();
	ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();
	
	//collect apps present in all open goals
	ImmutableSet<NoPosTacletApp> allApps 
		= proof.openGoals()
		       .head()
		       .ruleAppIndex()
		       .tacletIndex()
		       .allNoPosTacletApps();
	for(Goal goal : proof.openGoals().tail()) {
	    allApps = allApps.intersect(goal.ruleAppIndex()
		    		            .tacletIndex()
		    		            .allNoPosTacletApps());
	}
	
	//identify those apps suitable for the one step simplifier; 
	//store them in appsTakenOver and their taclets in result
	for(NoPosTacletApp app : allApps) {
	    final Taclet tac = app.taclet();
	    if(!(tac instanceof RewriteTaclet)
	       || !tac.hasReplaceWith()
	       || !tac.ifSequent().isEmpty()	       
	       || tac.goalTemplates().size() != 1
	       || !tac.goalTemplates().head().sequent().isEmpty()
	       || !tac.varsNew().isEmpty()
	       || tac.varsNewDependingOn().hasNext()
	       || ((RewriteTaclet)tac).getStateRestriction() 
	             != RewriteTaclet.NONE
	       || !proof.mgt().getJustification(app)
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
		result = result.add(tac);
	    }
	}
	
	//remove apps in appsTakenOver from taclet indices of all open goals
	for(NoPosTacletApp app : appsTakenOver) {
	    for(Goal goal : proof.openGoals()) {
		goal.ruleAppIndex().removeNoPosTacletApp(app);
	    }
	}
	
	return result;
    }
    
    
    /**
     * If the rule is applied to a different proof than last time, then clear
     * all caches and initialise the taclet indices.
     */
    private void initIndices(Proof proof) {
	if(proof != lastProof) {
	    shutdownIndices();
	    lastProof = proof;	    
	    appsTakenOver = DefaultImmutableSet.<NoPosTacletApp>nil();;	    
	    indices = new TacletIndex[ruleSets.size()];
	    notSimplifiableCaches = new LRUCache[indices.length];
	    int i = 0;
	    ImmutableList<String> done = ImmutableSLList.<String>nil();
	    for(String ruleSet : ruleSets) {
		ImmutableSet<Taclet> taclets = tacletsForRuleSet(proof, 
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
	    applicabilityCache.clear();
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
    private SequentFormula simplifyPos(Services services,
	  	        		   PosInOccurrence pos,
	  	        		   int indexNr) {
	final ImmutableList<NoPosTacletApp> apps 
		= indices[indexNr].getRewriteTaclet(pos, 
						    TacletFilter.TRUE, 
						    services);
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
	    SequentFormula result = taclet.getRewriteResult(services, app);
	    return result;
	}
	return null;
    }
    
    
    /**
     * Helper for simplifyPosOrSub. Performs a single step of simplification 
     * recursively at a subterm of the given position using the given taclet 
     * index.
     */    
    private SequentFormula simplifySub(Services services,
		   			   PosInOccurrence pos,
		   			   int indexNr) {
	for(int i = 0, n = pos.subTerm().arity(); i < n; i++) {
	    SequentFormula result 
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
    private SequentFormula simplifyPosOrSub(Services services,
	    		     	  	        PosInOccurrence pos,
	    		     	  	        int indexNr) {
	final Term term = pos.subTerm();
	if(notSimplifiableCaches[indexNr].get(term) != null) {
	    return null;
	}
	
	SequentFormula result;
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
    private SequentFormula replaceKnown(
	    				Services services, 
	                             	SequentFormula cf,
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
	    return new SequentFormula(simplifiedFormula);
	}
    }
    	   
    
    /**
     * Simplifies the passed constrained formula using a single taclet or 
     * arbitrarily many replace-known steps.
     */
    private SequentFormula simplifyConstrainedFormula(
	    				Services services,
	    				SequentFormula cf,
	    				Map<Term,PosInOccurrence> context,
	    				/*out*/ List<PosInOccurrence> ifInsts) {
	SequentFormula result 
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
	    				       SequentFormula cf,
	    				       Sequent seq) {
	//collect context formulas (potential if-insts for replace-known)
	final Map<Term,PosInOccurrence> context 
		= new HashMap<Term,PosInOccurrence>();
	for(SequentFormula ante : seq.antecedent()) {
	    if(!ante.equals(cf) && ante.formula().op() != Junctor.TRUE) {
		context.put(
			ante.formula(), 
			new PosInOccurrence(ante, PosInTerm.TOP_LEVEL, true));
	    }
	}
	for(SequentFormula succ : seq.succedent()) {
	    if(!succ.equals(cf) && succ.formula().op() != Junctor.FALSE) {
		context.put(
			succ.formula(), 
			new PosInOccurrence(succ, PosInTerm.TOP_LEVEL, false));
	    }
	}
	final List<PosInOccurrence> ifInsts 
		= new ArrayList<PosInOccurrence>(seq.size());
	
	//simplify as long as possible
	ImmutableList<SequentFormula> list 
		= ImmutableSLList.<SequentFormula>nil();
	SequentFormula simplifiedCf = cf;
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
     * Tells whether the passed formula can be simplified
     */
    private boolean applicableTo(Services services, SequentFormula cf) {
	final Boolean b = applicabilityCache.get(cf);
	if(b != null) {
	    return b.booleanValue();
	} else {
	    //try one simplification step without replace-known
	    final SequentFormula simplifiedCf 
	    	= simplifyConstrainedFormula(services, cf, null, null);
	    final boolean result = simplifiedCf != null 
	    			   && !simplifiedCf.equals(cf);
	    applicabilityCache.put(cf, Boolean.valueOf(result));
	    return result;
	}
    }
    
    

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public void refresh(Proof proof) {
	active = ProofSettings.DEFAULT_SETTINGS
		              .getGeneralSettings()
		              .oneStepSimplification();
	if(active && proof != null && !proof.closed()) {
	    initIndices(proof);
	} else {
	    shutdownIndices();	    
	}
    }
    
    
    @Override    
    public boolean isApplicable(Goal goal, 
                                PosInOccurrence pio) {
	//abort if switched off
	if(!active) {
	    return false;
	}	
	
	//abort if not top level constrained formula
	if(pio == null || !pio.isTopLevel()) {
	    return false;
	}
	
	//applicable to the formula?
	return applicableTo(goal.proof().getServices(), 
			    pio.constrainedFormula());
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
	final Instantiation inst 
		= computeInstantiation(services, 
			               pos.constrainedFormula(),
				       goal.sequent());
	
	//change goal, set if-insts
	resultGoal.changeFormula(inst.getCf(), pos);
	goal.setBranchLabel(inst.getNumAppliedRules() 
		            + (inst.getNumAppliedRules() > 1 
		               ? " rules" 
		               : " rule"));
	ruleApp = ((IBuiltInRuleApp)ruleApp).setIfInsts(inst.getIfInsts());
	
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
    
    
    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
	//don't care
    }

    
    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
	refresh(e.getSource().getSelectedProof());
    }
    
    
    

    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------
    
    private static final class Instantiation {	
	private final SequentFormula cf;
	private final int numAppliedRules;
	private final ImmutableList<PosInOccurrence> ifInsts;
		
	public Instantiation(SequentFormula cf, 
		             int numAppliedRules,
		             ImmutableList<PosInOccurrence> ifInsts) {
	    assert numAppliedRules >= 0;
	    this.cf = cf;
	    this.numAppliedRules = numAppliedRules;
	    this.ifInsts = ifInsts;
	}
	
	public SequentFormula getCf() {
	    return cf;
	}
	
	public int getNumAppliedRules() {
	    return numAppliedRules;
	}
	
	public ImmutableList<PosInOccurrence> getIfInsts() {
	    return ifInsts;
	}
	
	public String toString() {
	    return cf + " (" + numAppliedRules 
	              + (numAppliedRules > 1 ? " rules)" : "rule)");
	}
    }

	@Override
    public DefaultBuiltInRuleApp createApp(PosInOccurrence pos) {
	    return new DefaultBuiltInRuleApp(this, pos);
    }
}
