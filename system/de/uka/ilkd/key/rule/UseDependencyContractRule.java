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
import java.util.Map;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.util.InvInferenceTools;


public final class UseDependencyContractRule implements BuiltInRule {
    
    public static final UseDependencyContractRule INSTANCE 
                                            = new UseDependencyContractRule();    

    private static final Name NAME = new Name("Insert Dependency Contract");
    private static final TermBuilder TB = TermBuilder.DF;
    private static final InvInferenceTools IIT 
    	= InvInferenceTools.INSTANCE;
    

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private UseDependencyContractRule() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    

    

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
        final Operator op = pio.subTerm().op();
        final SpecificationRepository specRepos 
        	= goal.proof().getServices().getSpecificationRepository();
        DependencyContract depContract 
        	= specRepos.getDependencyContract(op);
        return depContract != null;
    }

    
    @Override    
    public ImmutableList<Goal> apply(Goal goal, 
	    			     Services services, 
	    			     RuleApp ruleApp) {
	//collect information
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final SortedOperator obs = (SortedOperator)ruleApp.posInOccurrence().subTerm().op();
        final SpecificationRepository specRepos 
        	= goal.proof().getServices().getSpecificationRepository();
        final DependencyContract depContract 
        	= specRepos.getDependencyContract(obs);
        assert depContract != null;
        
        assert obs.arity() == 2 : "not implemented";
        
        //create dependency formula
        final LogicVariable selfVar  = new LogicVariable(new Name("x"), depContract.getKJT().getSort());
        final LogicVariable heapVar1 = new LogicVariable(new Name("h1"), heapLDT.targetSort());
        final LogicVariable heapVar2 = new LogicVariable(new Name("h2"), heapLDT.targetSort());
        final LogicVariable objVar   = new LogicVariable(new Name("o"), services.getJavaInfo().objectSort());
        final LogicVariable fieldVar = new LogicVariable(new Name("f"), heapLDT.getFieldSort());
        Term dep = depContract.getDependencies(selfVar, services);        
        Map map = new HashMap();
        map.put(heapLDT.getHeap(), heapVar1);
        OpReplacer or = new OpReplacer(map);
        dep = or.replace(dep);
        
        final Term depFormula 
                = TB.all(new LogicVariable[]{selfVar, heapVar1, heapVar2},
        		 TB.imp(TB.all(new LogicVariable[]{objVar,fieldVar},
        			       TB.or(TB.elementOf(services, TB.pair(services, TB.var(objVar), TB.var(fieldVar)), dep),
        				     TB.equals(TB.select(services, Sort.ANY, TB.var(heapVar1), TB.var(objVar), TB.var(fieldVar)),
        				               TB.select(services, Sort.ANY, TB.var(heapVar2), TB.var(objVar), TB.var(fieldVar))))),
        			TB.equals(TB.tf().createTerm(obs, new Term[]{TB.var(heapVar1), TB.var(selfVar)}),
        				  TB.tf().createTerm(obs, new Term[]{TB.var(heapVar2), TB.var(selfVar)}))));
        		 
        //change goal
        final ImmutableList<Goal> newGoals = goal.split(1);
        final Goal newGoal = newGoals.head();
        final ConstrainedFormula cf = new ConstrainedFormula(depFormula);
        final PosInOccurrence pio = new PosInOccurrence(cf, PosInTerm.TOP_LEVEL, true);
        newGoal.addFormula(cf, pio);
        
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
