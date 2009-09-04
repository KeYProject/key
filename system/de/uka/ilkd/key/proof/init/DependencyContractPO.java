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

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.*;
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
    
//    /**
//     * Builds the "general assumption". 
//     */
//    private Term buildFreePre(ProgramVariable selfVar,
//	                      KeYJavaType selfKJT,
//                              ImmutableList<ProgramVariable> paramVars) 
//    		throws ProofInputException {
//
//        //"self != null"
//        final Term selfNotNull 
//            = selfVar == null
//              ? TB.tt()
//              : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
//        	      
//        //"self.<created> = TRUE"
//        final Term selfCreated
//           = selfVar == null
//             ? TB.tt()
//             : TB.created(services, TB.var(selfVar));
//             
//        //"MyClass::exactInstance(self) = TRUE"
//        final Term selfExactType
//           = selfVar == null
//             ? TB.tt()
//             : TB.exactInstance(services, 
//        	                selfKJT.getSort(), 
//        	                TB.var(selfVar));
//        
//        //conjunction of... 
//        //- "p_i.<created> = TRUE | p_i = null" for object parameters, and
//        //- "inBounds(p_i)" for integer parameters
//        Term paramsOK = TB.tt();
//        for(ProgramVariable paramVar : paramVars) {
//            paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
//        }
//        
//        //class axioms
//        final ImmutableSet<ClassAxiom> axioms 
//        	= specRepos.getClassAxioms(selfKJT);
//        Term axiomTerm = TB.tt();
//        for(ClassAxiom ax : axioms) {
//            Taclet axiomTaclet = ax.getAxiomAsTaclet(selfVar, services);
//            if(axiomTaclet != null) {
//        	taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(
//        							axiomTaclet));
//        	initConfig.getProofEnv()
//        	          .registerRule(axiomTaclet,
//        	        	        AxiomJustification.INSTANCE);
//            } else {
//        	axiomTerm = TB.and(axiomTerm, 
//        			   TB.forallHeaps(services, 
//        				   	  ax.getAxiom(selfVar, 
//        				   		      services)));
//            }
//        }
//        
//        return TB.and(new Term[]{TB.inReachableState(services), 
//        	       		 selfNotNull,
//        	       		 selfCreated,
//        	       		 selfExactType,
//        	       		 paramsOK,
//        	       		 axiomTerm});
//    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------        
    
    @Override
    public void readProblem() throws ProofInputException {
	final ObserverFunction target = contract.getTarget();
	assert false : "not implemented";
	
//        //prepare variables, program method, heapAtPre
//        final ImmutableList<ProgramVariable> paramVars 
//        	= TB.paramVars(services, pm, true);
//        final ProgramVariable selfVar 
//        	= TB.selfVar(services, pm, contract.getKJT(), true);
//        final ProgramVariable resultVar = TB.resultVar(services, pm, true);
//        final ProgramVariable exceptionVar = TB.excVar(services, pm, true);
//     	final LocationVariable heapAtPreVar 
//		= TB.heapAtPreVar(services, "heapAtPre", true);
//        final Term heapAtPre = TB.var(heapAtPreVar);
//
//        //build precondition
//        final Term pre = TB.and(buildFreePre(selfVar, 
//        	                             contract.getKJT(), 
//        	                             paramVars), 
//        	                contract.getPre(selfVar, paramVars, services)); 
//                
//        //build program term
//        final Term post = TB.and(contract.getPost(selfVar, 
//                                    	   	  paramVars, 
//                                    	   	  resultVar, 
//                                    	   	  exceptionVar,
//                                    	   	  heapAtPre,
//                                    	   	  services),
//                                 TB.frame(services, 
//                                	  heapAtPre, 
//                                	  contract.getMod(selfVar, 
//                                		  	  paramVars, 
//                                		  	  services)));
//        final Term progPost = buildProgramTerm(paramVars,
//                                               selfVar,
//                                               resultVar,
//                                               exceptionVar,
//                                               heapAtPreVar,
//                                               post);
//        
//        //save in field
//        poTerms = new Term[]{TB.imp(pre, progPost)};
//        poTaclets = new ImmutableSet[]{taclets};        
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