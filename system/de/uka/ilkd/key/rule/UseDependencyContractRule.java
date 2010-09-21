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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.InvInferenceTools;
import de.uka.ilkd.key.util.Pair;


public final class UseDependencyContractRule implements BuiltInRule {
    
    public static final UseDependencyContractRule INSTANCE 
                                            = new UseDependencyContractRule();    

    private static final Name NAME = new Name("Use Dependency Contract");
    private static final TermBuilder TB = TermBuilder.DF;
    private static final InvInferenceTools IIT = InvInferenceTools.INSTANCE;
    
            

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private UseDependencyContractRule() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Term getEqualityDef(Term term, Sequent seq) {
	for(ConstrainedFormula cf : seq.antecedent()) {
	    Term formula = cf.formula();
	    if(formula.op() instanceof Equality 
	       && formula.sub(1).equals(term)) {
		return formula.sub(0);
	    }
	}
	return null;
    }
    
    
    private Pair<Term,PosInOccurrence> getEqualityDefAndPos(Term term, 
	    						    Sequent seq) {
	for(ConstrainedFormula cf : seq.antecedent()) {
	    Term formula = cf.formula();
	    if(formula.op() instanceof Equality 
	       && formula.sub(1).equals(term)) {
		final PosInOccurrence pos 
			= new PosInOccurrence(cf, PosInTerm.TOP_LEVEL, true);
		return new Pair<Term,PosInOccurrence>(formula.sub(0), pos);
	    }
	}
	return null;
    }    
    
    
    private ImmutableSet<Term> addEqualDefs(ImmutableSet<Term> terms, Goal g) {
	ImmutableSet<Term> result = terms;
	for(ConstrainedFormula cf : g.sequent().antecedent()) {
	    final Term formula = cf.formula();
	    if(formula.op() instanceof Equality 
	        && terms.contains(formula.sub(1))) {
		result = result.add(formula.sub(0));
	    }
	}
	return result;
    }    
    
    
    private boolean hasRawSteps(Term heapTerm, Sequent seq, Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Operator op = heapTerm.op();
	assert heapTerm.sort().equals(heapLDT.targetSort());
	if(op == heapLDT.getStore()
	   || op == heapLDT.getCreate()
           || op == heapLDT.getAnon() 
	   || op == heapLDT.getMemset()) {
	   return true;
	} else if(op.arity() == 0) {
	    final Term def = getEqualityDef(heapTerm, seq);
	    if(def != null) {
		return hasRawSteps(def, seq, services);
	    } else {
		return false;
	    }
	} else {
	    return false;
	}
    }    
    
    
    private void getRawSteps(Term heapTerm, 
	    		     Sequent seq, 
	    		     Services services, 
	    		     List<Term> result) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Operator op = heapTerm.op();
	assert heapTerm.sort().equals(heapLDT.targetSort());
	if(op == heapLDT.getStore()
           || op == heapLDT.getCreate()
  	   || op == heapLDT.getAnon()
           || op == heapLDT.getMemset()) {
	    final Term h = heapTerm.sub(0);
	    result.add(h);	    
	    getRawSteps(h, seq, services, result);
	} else if(op.arity() == 0) {
	    final Term def = getEqualityDef(heapTerm, seq);
	    if(def != null) {
		getRawSteps(def, seq, services, result);
	    }
	}
    }
    
    
    private PosInOccurrence getFreshLocsStep(PosInOccurrence heapPos, 
	    				     Sequent seq, 
	    				     Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
	final Term heapTerm = heapPos.subTerm();
	final Operator op = heapTerm.op();
	assert heapTerm.sort().equals(heapLDT.targetSort());
	if(heapTerm.op() == heapLDT.getAnon()
	   && heapTerm.sub(1).op().equals(locSetLDT.getEmpty())) {
	    return heapPos;
	} else if(op.arity() == 0) {
	    final Pair<Term,PosInOccurrence> def 
	    	= getEqualityDefAndPos(heapTerm, seq);
	    if(def != null) {
		final PosInOccurrence defHeapPos = def.second.down(0);
		assert defHeapPos.subTerm().equals(def.first);
		return getFreshLocsStep(defHeapPos, seq, services);
	    } else {
		return null;
	    }
	} else {
	    return null;
	}
    }
    
    
    private Pair<Term,ImmutableList<PosInOccurrence>> 
    		 getChangedLocsForStep(Term heapTerm, 
	                       	       Term stepHeap, 
	                       	       Sequent seq,
	                       	       Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Operator op = heapTerm.op();
	assert heapTerm.sort().equals(heapLDT.targetSort());
	if(heapTerm.equals(stepHeap)) {
	    return new Pair<Term,ImmutableList<PosInOccurrence>>(
		    		TB.empty(services), 
		    		ImmutableSLList.<PosInOccurrence>nil());
	} else if(op == heapLDT.getStore()) {
	    final Term h = heapTerm.sub(0);
	    final Term o = heapTerm.sub(1);
	    final Term f = heapTerm.sub(2);
	    final Term locs = TB.singleton(services, o, f);
	    final Pair<Term,ImmutableList<PosInOccurrence>> furtherLocs 
	    	= getChangedLocsForStep(h, stepHeap, seq, services);
	    return new Pair<Term,ImmutableList<PosInOccurrence>>(
		    	    TB.union(services, locs, furtherLocs.first), 
		    	    furtherLocs.second);	    
	} else if(op == heapLDT.getCreate()) {
	    final Term h = heapTerm.sub(0);
	    final Pair<Term,ImmutableList<PosInOccurrence>> furtherLocs 
	    	= getChangedLocsForStep(h, stepHeap, seq, services);
	    return furtherLocs;
	} else if(op == heapLDT.getAnon() || op == heapLDT.getMemset()) {
	    final Term h = heapTerm.sub(0);
	    final Term s = heapTerm.sub(1);
	    final Pair<Term,ImmutableList<PosInOccurrence>> furtherLocs 
	    	= getChangedLocsForStep(h, stepHeap, seq, services);
	    return new Pair<Term,ImmutableList<PosInOccurrence>>(
		    	    TB.union(services, s, furtherLocs.first), 
	                    furtherLocs.second); 
	} else if(op.arity() == 0) {
	    final Pair<Term,PosInOccurrence> def 
	    	= getEqualityDefAndPos(heapTerm, seq);
	    if(def != null) {
		final Pair<Term,ImmutableList<PosInOccurrence>> furtherLocs
		    = getChangedLocsForStep(def.first, stepHeap, seq, services);
		return new Pair<Term,ImmutableList<PosInOccurrence>>(
				furtherLocs.first, 
			        furtherLocs.second.prepend(def.second));
	    }
	}
	assert false;
	return null;
    }
    
    
    public boolean isBaseOcc(Term focus, Term candidate) {
	if(!candidate.op().equals(focus.op())) {
	    return false;
	}
	for(int i = 1, n = candidate.arity(); i < n; i++) {
	    if(!(candidate.sub(i).equals(focus.sub(i)) 
		 || candidate.sub(i).op() instanceof LogicVariable)) {
		return false;
	    }
	}
	return true;
    }    
    
    
    private void collectBaseOccsHelper(Term focus, 
	    			       PosInOccurrence pos,
    				       Map<Term, PosInOccurrence> result) {
	final Term candidate = pos.subTerm();
	if(isBaseOcc(focus, candidate)) {
	    result.put(candidate.sub(0), pos);
	}
	for(int i = 0, n = candidate.arity(); i < n; i++) {
	    collectBaseOccsHelper(focus, pos.down(i), result);
	}
    }
    
    
    private Map<Term, PosInOccurrence> collectBaseOccs(Term focus, 
	    					       Sequent seq) {
	assert focus.op() instanceof ObserverFunction;
	final Map<Term, PosInOccurrence> result 
		= new HashMap<Term, PosInOccurrence>();
	for(ConstrainedFormula cf : seq.antecedent()) {
	    final PosInOccurrence pos 
	    	= new PosInOccurrence(cf, PosInTerm.TOP_LEVEL, true);
	    collectBaseOccsHelper(focus, pos, result);
	}
	for(ConstrainedFormula cf : seq.succedent()) {
	    final PosInOccurrence pos 
	    	= new PosInOccurrence(cf, PosInTerm.TOP_LEVEL, false);
	    collectBaseOccsHelper(focus, pos, result);
	}	
	return result;
    }    
    
    
    public List<PosInOccurrence> getSteps(PosInOccurrence pos,
	    				  Sequent seq,
	    				  Services services) {
	final Term focus = pos.subTerm();
	assert focus.op() instanceof ObserverFunction;
	
	final List<PosInOccurrence> result 
		= new LinkedList<PosInOccurrence>();
	
	//special treatment for anon(h, empty, h')
	final PosInOccurrence freshLocsStep 
		= getFreshLocsStep(pos.down(0), seq, services);
	if(freshLocsStep != null) {
	    result.add(freshLocsStep);
	    return result;
	}
	
	//get raw steps
	final List<Term> rawSteps = new LinkedList<Term>();
	getRawSteps(focus.sub(0), seq, services, rawSteps);
	if(rawSteps.size() > 0) {
	    //get base occs
	    final Map<Term, PosInOccurrence> baseOccs 
	    	= collectBaseOccs(focus, seq);

	    //filter steps
	    for(Term rawStep : rawSteps) {
		final PosInOccurrence step = baseOccs.get(rawStep);
		if(step != null) {
		    result.add(step);
		}
	    }
	}
	
	return result;
    }
    
    

    private PosInOccurrence findStepInIfInsts(
	    		List<PosInOccurrence> steps,
	    		BuiltInRuleApp app,
	    		Services services) {
	for(PosInOccurrence pio : app.ifInsts()) {
	    if(steps.contains(pio)) {
		return pio;
	    }
	}
	return null;
    }
        
    
    
    private PosInOccurrence letUserChooseStep(
	    		List<PosInOccurrence> steps, 
	    		Services services) {
	//prepare array of possible base heaps
	final Term[] heaps = new Term[steps.size()];
	int i = 0;
	for(PosInOccurrence step : steps) {
	    heaps[i++] = step.subTerm().sub(0);
	}
	
	//open dialog
	final Term heap 
		= (Term)JOptionPane.showInputDialog(
				Main.getInstance(),
				"Please select a base heap:",
				"Instantiation",
				JOptionPane.QUESTION_MESSAGE,
				null,
				heaps,
				heaps.length > 0 ? heaps[0] : null);
	if(heap == null) {
	    return null;
	}
	
	//find corresponding step
	for(PosInOccurrence step : steps) {
	    if(step.subTerm().sub(0).equals(heap)) {
		return step;
	    }
	}
	assert false;
	return null;
    }
    
    
    private Pair<Term,Term> getBaseHeapAndChangedLocs(
	    			PosInOccurrence pos,
	    			Sequent seq,
	    			Services services,
	    			BuiltInRuleApp app) {
	final Term focus = pos.subTerm();
	assert app != null;
	assert focus.op() instanceof ObserverFunction;
	
	//get possible steps
	final List<PosInOccurrence> steps = getSteps(pos, seq, services);
	
	//choose a step
	final PosInOccurrence step;
	if(Main.getInstance().mediator().autoMode()) {
	    step = findStepInIfInsts(steps, app, services);
	    assert step != null 
	           : "The strategy failed to properly "
	              + "instantiate the base heap!\n"
	              + "at: " + app.posInOccurrence().subTerm() + "\n"
	              + "ifInsts: " + app.ifInsts() + "\n"
	              + "steps: " + steps;
	} else {
	    step = letUserChooseStep(steps, services);
	    if(step == null) {
		return null;
	    }
	}
	assert !step.equals(focus);
	
	//get changed locs and used equalities
	final Pair<Term,ImmutableList<PosInOccurrence>> changedLocs 
		= getChangedLocsForStep(focus.sub(0), 
					step.subTerm().sub(0), 
					seq, 
					services);
	
	//store insts in rule app
	app.setIfInsts(changedLocs.second.prepend(step));

	//return step heap and changed locs
	return new Pair<Term,Term>(step.subTerm().sub(0), changedLocs.first);
    }
    
    
    /**
     * Returns the dependency contracts which are applicable for the passed 
     * target.
     */
    private ImmutableSet<Contract> getApplicableContracts(
	    					Services services,  
                                                KeYJavaType kjt,
                                                ObserverFunction target) {
        ImmutableSet<Contract> result 
        	= services.getSpecificationRepository().getContracts(kjt, 
        							     target);
        for(Contract contract : result) {
            if(!contract.hasDep()) {
        	result = result.remove(contract);
            }
        }
        return result;
    }
    
    
    /**
     * Chooses a contract to be applied. 
     */
    private Contract configureContract(Services services, 
                                       KeYJavaType kjt,
                                       ObserverFunction target) {
	final ImmutableSet<Contract> contracts
                = getApplicableContracts(services, kjt, target);
	assert !contracts.isEmpty();
	return contracts.iterator().next();//TODO
    }
    
        
        

    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    @Override
    public boolean isApplicable(Goal goal, 
                                PosInOccurrence pio, 
                                Constraint userConstraint) {
	if(pio == null) {
	    return false;
	}
	
	//top level symbol must be observer
	final Term focus = pio.subTerm();
	if(!(focus.op() instanceof ObserverFunction)) {
	    return false;
	}
	
	//there must not be free variables in the focus term
	if(!focus.freeVars().isEmpty()) {
	    return false;
	}

	//heap term of observer must be store-term
	final Services services = goal.proof().getServices();
	if(!hasRawSteps(focus.sub(0), goal.sequent(), services)) {
	    return false;
	}

	//there must be contracts for the observer
	final ObserverFunction target = (ObserverFunction) focus.op();
	final KeYJavaType kjt 
		= target.isStatic() 
		  ? target.getContainerType()
	          : services.getJavaInfo().getKeYJavaType(focus.sub(1).sort());
	assert kjt != null : "could not determine receiver type for " + focus;
	if(kjt.getSort() instanceof NullSort) {
	    return false;
	}
        final ImmutableSet<Contract> contracts 
        	= getApplicableContracts(services, kjt, target);
        if(contracts.isEmpty()) {
            return false;
        }
        
        //applying a contract here must not create circular dependencies 
        //between proofs
        if(!goal.proof().mgt().contractApplicableFor(kjt, target)) {
            return false;
        }
        
        return true;
    }

    
    @Override    
    public ImmutableList<Goal> apply(Goal goal,
	    			     Services services,
	    			     RuleApp ruleApp) {		
	//collect information
	final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
	final PosInOccurrence pio = ruleApp.posInOccurrence();	
        final Term focus = pio.subTerm();
        final ObserverFunction target = (ObserverFunction) focus.op();
        final Term selfTerm = target.isStatic() ? null : focus.sub(1);
        ImmutableList<Term> paramTerms = ImmutableSLList.<Term>nil();
        for(int i = target.isStatic() ? 1 : 2, n = focus.arity(); i < n; i++) {
            paramTerms = paramTerms.append(focus.sub(i));
        }
        final KeYJavaType kjt
        	= target.isStatic() 
		  ? target.getContainerType()
	          : services.getJavaInfo().getKeYJavaType(selfTerm.sort());
        final Contract contract = configureContract(services, kjt, target);
        assert contract != null;
        final Pair<Term,Term> baseHeapAndChangedLocs 
        	= getBaseHeapAndChangedLocs(pio, 
        				    goal.sequent(), 
        				    services, 
        				    (BuiltInRuleApp)ruleApp);
        if(baseHeapAndChangedLocs == null) {
            return goal.split(1);
        }
        
        //get precondition, dependency term
        Term freePre 
        	= TB.and(TB.wellFormed(services, baseHeapAndChangedLocs.first),
        		 TB.wellFormed(services, focus.sub(0)));
	if(!target.isStatic()) {
	    freePre = TB.and(freePre, TB.not(TB.equals(selfTerm, TB.NULL(services))));
	    freePre = TB.and(freePre, TB.created(services,
				                 baseHeapAndChangedLocs.first,
        	                    		 selfTerm));
	}
	int i = 0;
	for(Term paramTerm : paramTerms) {
	    freePre = TB.and(freePre, TB.reachableValue(services,
					       		baseHeapAndChangedLocs.first,
					       		paramTerm, 
					       		target.getParamType(i++)));
	}
        final Term pre = contract.getPre(baseHeapAndChangedLocs.first,
        	                         selfTerm, 
        	                         paramTerms, 
        	                         services);
        final Term dep = contract.getDep(baseHeapAndChangedLocs.first, 
        				 selfTerm, 
        				 paramTerms, 
        				 services);
        final Term disjoint 
        	= TB.disjoint(services, baseHeapAndChangedLocs.second, dep);
        final Term cutFormula = TB.and(new Term[]{freePre, pre, disjoint});
        
        //bail out if obviously not helpful
        if(!baseHeapAndChangedLocs.second.op().equals(locSetLDT.getEmpty())) {
            final ImmutableSet<Term> changed 
            	= addEqualDefs(IIT.unionToSet(baseHeapAndChangedLocs.second, 
            				      services), 
            				      goal);
            if(changed.contains(dep)) {
        	return goal.split(1);
            }
        }
        
        //split goal into two branches
        final ImmutableList<Goal> result = goal.split(2);
        final Goal preGoal = result.head();
        final Goal postGoal = result.tail().head();
        final String changeString 
        	= LogicPrinter.quickPrintTerm(baseHeapAndChangedLocs.second, 
        				      services);
        preGoal.setBranchLabel("Dependencies changed by write to " 
        	               + changeString);
        postGoal.setBranchLabel("Dependencies unchanged by write to " 
        	                + changeString);
        
        //create "Pre" branch
        preGoal.addFormula(new ConstrainedFormula(cutFormula),
        		   false,
        		   true);
        
        //create "Post" branch
        final Term[] subs = focus.subs().toArray(new Term[focus.arity()]);
        subs[0] = baseHeapAndChangedLocs.first;
        final Term termWithBaseHeap = TB.func(target, subs);
        postGoal.addFormula(new ConstrainedFormula(TB.equals(focus, termWithBaseHeap)), true, false);
        postGoal.addFormula(new ConstrainedFormula(cutFormula),
        	 	    true,
        	 	    false);
        
        //create justification
        final RuleJustificationBySpec just 
        	= new RuleJustificationBySpec(contract);
        final ComplexRuleJustificationBySpec cjust 
            	= (ComplexRuleJustificationBySpec)
            	    goal.proof().env().getJustifInfo().getJustification(this);
        cjust.add(ruleApp, just);
        
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
}
