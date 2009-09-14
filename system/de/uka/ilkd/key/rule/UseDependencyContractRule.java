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

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
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
    
    
    private Pair<Term,Term> getBaseHeapAndChangedLocs(
	    			Term heapTerm,
	    			Sequent seq,
	    			Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Operator op = heapTerm.op();
	if(op == heapLDT.getStore()) {
	    final Term h = heapTerm.sub(0);
	    final Term o = heapTerm.sub(1);
	    final Term f = heapTerm.sub(2);
	    return new Pair<Term,Term>(h, TB.pairSingleton(services, o, f));
	} else if(op == heapLDT.getChangeHeapAtLocs() 
		  || op == heapLDT.getChangeHeapAtLocs2()) {
	    final Term h = heapTerm.sub(0);
	    final Term s = heapTerm.sub(1);
	    return new Pair<Term,Term>(h, s); 
	} else if(op.arity() == 0) {
	    final Term def = getEqualityDef(heapTerm, seq);
	    if(def != null) {
		return getBaseHeapAndChangedLocs(def, seq, services);
	    } else {
		return null;
	    }
	} else {
	    return null;
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
	final Pair<Term,Term> baseHeapAndChangedLocs 
		= getBaseHeapAndChangedLocs(term.sub(0), 
			                    goal.sequent(), 
			                    services);
	if(baseHeapAndChangedLocs == null) {
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
        	= getBaseHeapAndChangedLocs(heap, goal.sequent(), services); 
        
        //get precondition, dependency term
        final Term pre = contract.getPre(baseHeapAndChangedLocs.first,
        	                         selfTerm, 
        	                         paramTerms, 
        	                         services);
        final Term dep = contract.getDep(baseHeapAndChangedLocs.first, 
        				 selfTerm, 
        				 paramTerms, 
        				 services);
        final Term changedLocsAndDepDisjoint 
        	= TB.disjoint(services, baseHeapAndChangedLocs.second, dep);
        
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
        preGoal.addFormula(new ConstrainedFormula(
        				TB.and(pre, changedLocsAndDepDisjoint)),
        		   false,
        		   true);
        
        //create "Post" branch
        final Term[] subs = term.subs().toArray(new Term[term.arity()]);
        subs[0] = baseHeapAndChangedLocs.first;
        final Term termWithBaseHeap = TB.func(target, subs);
        postGoal.addFormula(new ConstrainedFormula(TB.equals(term, termWithBaseHeap)), true, false);
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
