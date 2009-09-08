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

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.Pair;


public final class UseDependencyContractRule implements BuiltInRule {
    
    public static final UseDependencyContractRule INSTANCE 
                                            = new UseDependencyContractRule();    

    private static final Name NAME = new Name("Use Dependency Contract");
    private static final TermBuilder TB = TermBuilder.DF;
        

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private UseDependencyContractRule() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Pair<Term,Term> getBaseHeapAndChangedLocs(Term heapTerm,
	    					      Services services,
	                                              HeapLDT heapLDT) {
	Operator op = heapTerm.op();
	if(op == heapLDT.getStore()) {
	    final Term h = heapTerm.sub(0);
	    final Term o = heapTerm.sub(1);
	    final Term f = heapTerm.sub(2);
	    final Pair<Term,Term> sub
	    	= getBaseHeapAndChangedLocs(h, services, heapLDT);
	    return new Pair<Term,Term>(sub.first, 
		    		       TB.union(services, 
		    			        TB.pairSingleton(services, 
		    			        	         o, 
		    			        	         f),
		    			        sub.second));
	} else if(op == heapLDT.getChangeHeapAtLocs() 
		  || op == heapLDT.getChangeHeapAtLocs2()) {
	    final Term h = heapTerm.sub(0);
	    final Term s = heapTerm.sub(1);
	    final Pair<Term,Term> sub 
	    	= getBaseHeapAndChangedLocs(h, services, heapLDT);
	    return new Pair<Term,Term>(sub.first, 
				       TB.union(services, 
					        s,
					        sub.second));
	} else {
	    return new Pair<Term,Term>(heapTerm, TB.empty(services));
	}
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
     * This is done either automatically or by asking the user.
     */
    private Contract configureContract(Services services, 
                                       KeYJavaType kjt,
                                       ObserverFunction target) {
	final ImmutableSet<Contract> contracts
                = getApplicableContracts(services, kjt, target);
	assert !contracts.isEmpty();
	return contracts.iterator().next();//TODO
    }
    
    
    /**
     * Replaces all occurrences of "orig" by "replacement".
     */
    private void replaceInGoal(Term orig, Term replacement, Goal goal) {
        final Map<Term, Term> replaceMap = new LinkedHashMap<Term, Term>();
        replaceMap.put(orig, replacement);
        final OpReplacer or = new OpReplacer(replaceMap);
        
	final Sequent s = goal.sequent();        
	for(int i = 1, n = s.size(); i <= n; i++) {
	    ConstrainedFormula cf = s.getFormulabyNr(i);
	    Term formula = cf.formula();
	    Term newFormula = or.replace(formula);
	    if(!formula.equals(newFormula)) {
		goal.changeFormula(new ConstrainedFormula(newFormula), 
			           PosInOccurrence.findInSequent(
			        	   		s, 
			        	   		i, 
			        	                PosInTerm.TOP_LEVEL));
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
	if(pio == null) {
	    return false;
	}
	
	//top level symbol must be observer
	final Term term = pio.subTerm();
	if(!(term.op() instanceof ObserverFunction)) {
	    return false;
	}
	
	//there must not be free variables in the focus term
	if(!term.freeVars().isEmpty()) {
	    return false;
	}
	
	//heap term of observer must be store-term
	final Services services = goal.proof().getServices();		
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Pair<Term,Term> baseHeapAndChangedLocs 
		= getBaseHeapAndChangedLocs(term.sub(0), services, heapLDT);
	if(baseHeapAndChangedLocs.first.equals(term.sub(0))) {
	    return false;
	}
	
	//there must be contracts for the observer
	final ObserverFunction target = (ObserverFunction) term.op();
	final KeYJavaType kjt 
		= target.isStatic() 
		  ? target.getContainerType()
	          : services.getJavaInfo().getKeYJavaType(term.sub(1).sort());
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
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();	
	final PosInOccurrence pio = ruleApp.posInOccurrence();	
        final Term term = pio.subTerm();
        final ObserverFunction target = (ObserverFunction) term.op();
        final Term heap = term.sub(0);
        assert heap.sort().equals(heapLDT.targetSort());
        final Term selfTerm = target.isStatic() ? null : term.sub(1);
        ImmutableList<Term> paramTerms = ImmutableSLList.<Term>nil();
        for(int i = target.isStatic() ? 1 : 2, n = term.arity(); i < n; i++) {
            paramTerms = paramTerms.append(term.sub(i));
        }
        final KeYJavaType kjt
        	= target.isStatic() 
		  ? target.getContainerType()
	          : services.getJavaInfo().getKeYJavaType(selfTerm.sort());
        final Contract contract = configureContract(services, kjt, target);
        assert contract != null;	
        final Pair<Term,Term> baseHeapAndChangedLocs 
        	= getBaseHeapAndChangedLocs(heap, services, heapLDT); 
        
        //get precondition, dependency term
        final Term pre = contract.getPre(baseHeapAndChangedLocs.first,
        	                         selfTerm, 
        	                         paramTerms, 
        	                         services);
        final Term dep = contract.getDep(baseHeapAndChangedLocs.first, 
        				 selfTerm, 
        				 paramTerms, 
        				 services);
        
        //split goal into two branches
        final ImmutableList<Goal> result = goal.split(2);
        final Goal preGoal = result.head();//tail().head();
        final Goal postGoal = result.tail().head();
        preGoal.setBranchLabel("Dependencies changed");
        postGoal.setBranchLabel("Dependencies unchanged");
        
        //create "Pre" branch
        final Term changedLocsAndDepDisjoint 
        	= TB.disjoint(services, baseHeapAndChangedLocs.second, dep);
        preGoal.removeFormula(pio);
        preGoal.addFormula(new ConstrainedFormula(
        				TB.and(pre, changedLocsAndDepDisjoint)),
        		   false,
        		   true);
        
        //create "Post" branch
        final Term[] subs = term.subs().toArray(new Term[term.arity()]);
        subs[0] = baseHeapAndChangedLocs.first;
        final Term termWithBaseHeap = TB.func(target, subs);
        replaceInGoal(term, termWithBaseHeap, postGoal);
        postGoal.addFormula(new ConstrainedFormula(
        				TB.and(pre, changedLocsAndDepDisjoint)),
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
