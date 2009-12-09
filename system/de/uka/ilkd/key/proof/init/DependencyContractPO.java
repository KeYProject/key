// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.Iterator;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;


/**
 * The proof obligation for operation contracts. 
 */
public final class DependencyContractPO extends AbstractPO 
                                        implements ContractPO {
    
    private final Contract contract;
    
    private ImmutableSet<NoPosTacletApp> taclets 
    	= DefaultImmutableSet.<NoPosTacletApp>nil();
       
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public DependencyContractPO(InitConfig initConfig, Contract contract) {
    	super(initConfig, contract.getName());
    	this.contract = contract;
    	assert !(contract instanceof OperationContract);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------    
    
    private Term buildFreePre(ProgramVariable selfVar,
	                      KeYJavaType selfKJT,
	                      ImmutableList<ProgramVariable> paramVars) 
    		throws ProofInputException {
        //"self != null"
	final Term selfNotNull 
            = selfVar == null
              ? TB.tt()
              : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
              
        //"self.<created> = TRUE"
        final Term selfCreated
           = selfVar == null
             ? TB.tt()
             : TB.created(services, TB.var(selfVar));
	
        	      
        //"MyClass::exactInstance(self) = TRUE"
        final Term selfExactType
           = selfVar == null
             ? TB.tt()
             : TB.exactInstance(services, 
        	                selfKJT.getSort(), 
        	                TB.var(selfVar));
             
	
        //conjunction of... 
        //- "p_i.<created> = TRUE | p_i = null" for object parameters, and
        //- "inBounds(p_i)" for integer parameters
        Term paramsOK = TB.tt();
        for(ProgramVariable paramVar : paramVars) {
            paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
        }             
             
        //class axioms
        final ImmutableSet<ClassAxiom> axioms 
        	= specRepos.getClassAxioms(selfKJT);
        Term axiomTerm = TB.tt();
        for(ClassAxiom ax : axioms) {
            Taclet axiomTaclet = ax.getAxiomAsTaclet(services);
            if(axiomTaclet != null) {
        	taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(
        							axiomTaclet));
        	initConfig.getProofEnv()
        	          .registerRule(axiomTaclet,
        	        	        AxiomJustification.INSTANCE);
            } else {
        	axiomTerm = TB.and(axiomTerm, 
        			   TB.forallHeaps(services, 
        				   	  ax.getAxiom(services)));
            }
        }
        
        //connection between any::select and other::select
        for(Taclet taclet : initConfig.activatedTaclets()) {
            if(taclet.name().toString().equals("selectToAnySelect")) {
        	RewriteTaclet rt = (RewriteTaclet) taclet; 
        	RewriteTacletBuilder tb = new RewriteTacletBuilder();
        	tb.setFind(rt.find());
        	Iterator<VariableCondition> it = rt.getVariableConditions();
        	while(it.hasNext()) {
        	    tb.addVariableCondition(it.next());
        	}
        	for(TacletGoalTemplate template : rt.goalTemplates()) {
        	    tb.addTacletGoalTemplate(template);
        	}
        	tb.setName(new Name("selectToAnySelectAuto"));
        	tb.addRuleSet(new RuleSet(
        		  new Name("inReachableStateImplication")));
        	final Taclet autoTaclet = tb.getTaclet();
        	taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(
        						autoTaclet));
        	initConfig.getProofEnv()
        	          .registerRule(autoTaclet,
        	        	        AxiomJustification.INSTANCE);        	
            }
        }             
        
        return TB.and(new Term[]{TB.inReachableState(services), 
        	       		 selfNotNull,
        	       		 selfCreated,
        	       		 selfExactType,
        	       		 paramsOK,
        	       		 axiomTerm});        
    }    
    
    		

    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------        
    
    @Override
    public void readProblem() throws ProofInputException {
	ObserverFunction target = contract.getTarget();
	if(target instanceof ProgramMethod) {
	    target = javaInfo.getToplevelPM(contract.getKJT(), 
		    			    (ProgramMethod)target);
	}
	
	//prepare variables
	final ProgramVariable selfVar 
		= TB.selfVar(services, contract.getKJT(), true);
	final ImmutableList<ProgramVariable> paramVars
		= TB.paramVars(services, target, true);
	
	//translate contract
	final Term pre = TB.and(buildFreePre(selfVar, 
			                     contract.getKJT(), 
					     paramVars),
			        contract.getPre(selfVar, paramVars, services));
	final Term dep = contract.getDep(selfVar, paramVars, services);
	
	//prepare update
	final Name anonHeapName 
		= new Name(TB.newName(services, "anonHeap"));
	final Function anonHeapFunc = new Function(anonHeapName,
					           heapLDT.targetSort());
	final Term anonHeap = TB.func(anonHeapFunc);
	final Term changedHeap 
		= TB.anon(services, 
			              TB.heap(services), 
				      TB.setMinus(services, 
					          TB.everything(services), 
					          dep), 
	                              anonHeap);
	final Term update = TB.elementary(services, 
					  heapLDT.getHeap(), 
					  changedHeap);
	
	//prepare target term
	final Term[] subs
		= new Term[paramVars.size() + (target.isStatic() ? 1 : 2)];
	subs[0] = TB.heap(services);
	int offset = 1;
	if(!target.isStatic()) {
	    subs[1] = TB.var(selfVar);
	    offset++;
	}
	for(ProgramVariable paramVar : paramVars) {
	    subs[offset] = TB.var(paramVar);
	    subs[offset] = TB.var(paramVar);
	    offset++;
	}
	final Term targetTerm = TB.func(target, subs);
	
	//build po
	final Term po = TB.imp(pre,
                               TB.equals(targetTerm, 
                        	         TB.apply(update, targetTerm)));

        //save in field
        poTerms = new Term[]{po};
        poTaclets = new ImmutableSet[]{taclets};        
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        if(!(po instanceof DependencyContractPO)) {
            return false;
        }
        DependencyContractPO cPO = (DependencyContractPO) po;
        return contract.equals(cPO.contract);
    }
    
    
    @Override
    public Contract getContract() {
        return contract;
    }
   
    
    
    @Override
    public boolean equals(Object o) {
	if(!(o instanceof DependencyContractPO)) {
	    return false;
	} else {
	    return contract.equals(((DependencyContractPO)o).contract);
	}
    }
    
    
    @Override
    public int hashCode() {
        return contract.hashCode();
    }
}