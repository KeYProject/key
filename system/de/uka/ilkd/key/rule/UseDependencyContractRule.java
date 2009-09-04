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
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.speclang.Contract;


public final class UseDependencyContractRule implements BuiltInRule {
    
    public static final UseDependencyContractRule INSTANCE 
                                            = new UseDependencyContractRule();    

    private static final Name NAME = new Name("Insert Dependency Contract");
    private static final TermBuilder TB = TermBuilder.DF;
        

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private UseDependencyContractRule() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
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
	
	final Term term = pio.subTerm();
	if(!(term.op() instanceof ObserverFunction)) {
	    return false;
	}
	
	final Services services = goal.proof().getServices();	
	final ObserverFunction target = (ObserverFunction) term.op();
	final KeYJavaType kjt 
		= target.isStatic() 
		  ? target.getContainerType()
	          : services.getJavaInfo().getKeYJavaType(term.sub(1).sort());
        final ImmutableSet<Contract> contracts 
        	= getApplicableContracts(services, kjt, target);
        return !contracts.isEmpty();
    }

    
    @Override    
    public ImmutableList<Goal> apply(Goal goal, 
	    			     Services services, 
	    			     RuleApp ruleApp) {
	//collect information
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();	
        final Term term = ruleApp.posInOccurrence().subTerm();
        final ObserverFunction target = (ObserverFunction) term.op();
        final KeYJavaType kjt
        	= target.isStatic() 
		  ? target.getContainerType()
	          : services.getJavaInfo().getKeYJavaType(term.sub(1).sort());
        final Contract contract = configureContract(services, kjt, target);
        assert contract != null;	
        final Term heapTerm = term.sub(0);
        assert heapTerm.sort().equals(heapLDT.targetSort());
        final Term selfTerm = target.isStatic() ? null : term.sub(1);
        ImmutableList<Term> paramTerms = ImmutableSLList.<Term>nil();
        for(int i = target.isStatic() ? 1 : 2, n = term.arity(); i < n; i++) {
            paramTerms = paramTerms.append(term.sub(i));
        }
                
        //create logic variables
        final LogicVariable heapVar
        	= new LogicVariable(new Name("h"), heapLDT.targetSort());
        final LogicVariable objVar
        	= new LogicVariable(new Name("o"), 
        			    services.getJavaInfo().objectSort());
        final LogicVariable fieldVar 
        	= new LogicVariable(new Name("f"), heapLDT.getFieldSort());
        
        //get dependency term
        final Term secondHeapTerm = TB.var(heapVar);        
        final Term dep = OpReplacer.replace(TB.heap(services), 
        				    secondHeapTerm, 
        				    contract.getDep(selfTerm, 
        					            paramTerms, 
        					            services));

        //create dependency formula        
        final Term[] subs = term.subs().toArray(new Term[term.arity()]);
        subs[0] = secondHeapTerm;
        final Term secondTerm = TB.tf().createTerm(target, subs);
        
        final Term depFormula 
                        = TB.all(heapVar, 
                	     	TB.imp(TB.all(new LogicVariable[]{objVar,fieldVar},
        			       TB.imp(TB.elementOf(services, TB.pair(services, TB.var(objVar), TB.var(fieldVar)), dep),
        				      TB.equals(TB.select(services, Sort.ANY, heapTerm, TB.var(objVar), TB.var(fieldVar)),
        				                TB.select(services, Sort.ANY, secondHeapTerm, TB.var(objVar), TB.var(fieldVar))))),
        			TB.equals(term, secondTerm)));
        		 
        //change goal
        final ImmutableList<Goal> newGoals = goal.split(1);
        final Goal newGoal = newGoals.head();
        final ConstrainedFormula cf = new ConstrainedFormula(depFormula);
        newGoal.addFormula(cf, true, false);
        
        //create justification
        final RuleJustificationBySpec just 
        	= new RuleJustificationBySpec(contract);
        final ComplexRuleJustificationBySpec cjust 
            	= (ComplexRuleJustificationBySpec)
            	    goal.proof().env().getJustifInfo().getJustification(this);
        cjust.add(ruleApp, just);        
        
        return newGoals;
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
