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
import de.uka.ilkd.key.proof.OpReplacer;
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
    
    private Term buildFreePreNoHeap(ProgramVariable selfVar,
	                            KeYJavaType selfKJT,
	                            ImmutableList<ProgramVariable> paramVars) 
    		throws ProofInputException {
        //"self != null"
	final Term selfNotNull 
            = selfVar == null
              ? TB.tt()
              : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
        	      
        //"MyClass::exactInstance(self) = TRUE"
        final Term selfExactType
           = selfVar == null
             ? TB.tt()
             : TB.exactInstance(services, 
        	                selfKJT.getSort(), 
        	                TB.var(selfVar));
             
        //class axioms
        final ImmutableSet<ClassAxiom> axioms 
        	= specRepos.getClassAxioms(selfKJT);
        Term axiomTerm = TB.tt();
        for(ClassAxiom ax : axioms) {
            Taclet axiomTaclet = ax.getAxiomAsTaclet(selfVar, services);
            if(axiomTaclet != null) {
        	taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(
        							axiomTaclet));
        	initConfig.getProofEnv()
        	          .registerRule(axiomTaclet,
        	        	        AxiomJustification.INSTANCE);
            } else {
        	axiomTerm = TB.and(axiomTerm, 
        			   TB.forallHeaps(services, 
        				   	  ax.getAxiom(selfVar, 
        				   		      services)));
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
        
        return TB.and(new Term[]{selfNotNull, selfExactType, axiomTerm});
    }    
    
    
    private Term buildFreePreWithHeap(ProgramVariable selfVar,
	                              KeYJavaType selfKJT,
	                              ImmutableList<ProgramVariable> paramVars)
		throws ProofInputException {	
	//self.<created> = TRUE
	final Term selfCreated = TB.created(services, TB.var(selfVar)); 
	
        //conjunction of... 
        //- "p_i.<created> = TRUE | p_i = null" for object parameters, and
        //- "inBounds(p_i)" for integer parameters
        Term paramsOK = TB.tt();
        for(ProgramVariable paramVar : paramVars) {
            paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
        }
        
        return TB.and(new Term[]{TB.inReachableState(services), 
        	       		 selfCreated,
        	       		 paramsOK});
    }
    		

    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------        
    
    @Override
    public void readProblem() throws ProofInputException {
	final ObserverFunction target = contract.getTarget();
	
	//prepare variables
	final ProgramVariable selfVar 
		= TB.selfVar(services, contract.getKJT(), true);
	final ImmutableList<ProgramVariable> paramVars
		= TB.paramVars(services, target, true);
	final LogicVariable heapLV1 
		= new LogicVariable(new Name("h1"),  heapLDT.targetSort());
	final LogicVariable heapLV2 
		= new LogicVariable(new Name("h2"),  heapLDT.targetSort());
	final Term heapLV1Term = TB.var(heapLV1);
	final Term heapLV2Term = TB.var(heapLV2);
	final Term[] subs1
		= new Term[paramVars.size() + (target.isStatic() ? 1 : 2)];
	final Term[] subs2 = new Term[subs1.length];
	subs1[0] = heapLV1Term;
	subs2[0] = heapLV2Term;
	int offset = 1;
	if(!target.isStatic()) {
	    subs1[1] = TB.var(selfVar);
	    subs2[1] = TB.var(selfVar);
	    offset++;
	}
	for(ProgramVariable paramVar : paramVars) {
	    subs1[offset] = TB.var(paramVar);
	    subs2[offset] = TB.var(paramVar);
	    offset++;
	}
	final Term targetTerm1 = TB.func(target, subs1);
	final Term targetTerm2 = TB.func(target, subs2);
	
	//build po
	final Term indepPre = buildFreePreNoHeap(selfVar, 
						 contract.getKJT(), 
						 paramVars);
	final Term pre = TB.and(buildFreePreWithHeap(selfVar, 
        	                                     contract.getKJT(), 
        	                                     paramVars), 
        	                contract.getPre(selfVar, paramVars, services));
	final Term pre1 = OpReplacer.replace(TB.heap(services), 
					     heapLV1Term, 
					     pre);
	final Term pre2 = OpReplacer.replace(TB.heap(services), 
					     heapLV2Term, 
					     pre);
	final Term dep = OpReplacer.replace(TB.heap(services), 
		                            heapLV1Term, 
		                            contract.getDep(selfVar, 
		                        	    	    paramVars, 
		                        	    	    services));
	final Term po = TB.imp(TB.and(new Term[]{indepPre,
		                                 pre1,
		                                 pre2,
		                                 TB.unchanged(services, 
					    		      heapLV1Term, 
					    		      heapLV2Term, 
					    		      dep)}),
                               TB.equals(targetTerm1, targetTerm2));
		               
        //save in field
        poTerms = new Term[]{TB.all(new QuantifiableVariable[]{heapLV1, 
        	                                               heapLV2}, 
        	                    po)};
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