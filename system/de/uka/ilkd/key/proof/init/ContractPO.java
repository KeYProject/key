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
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.OperationContract;


/**
 * The "Ensures" proof obligation. 
 */
public final class ContractPO extends AbstractPO {
    
    private final OperationContract contract;
       
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public ContractPO(InitConfig initConfig, OperationContract contract) {
    	super(initConfig, 
    	      "ContractSatisfied: " + contract.getName(),
    	      contract.getProgramMethod().getContainerType());
    	this.contract = contract;
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------    

//    /**
//     * (helper for buildAssumedInvs())
//     */
//    private Term buildImplicitInvariantsForClass(KeYJavaType classKJT) 
//    		throws ProofInputException {
//	assert classKJT.getJavaType() instanceof ClassType;
//	
//        //"C.<classErroneous> = FALSE"
//	Term notErroneous
//	    = TB.equals(TB.dotClassErroneous(services, classKJT.getSort()), 
//		        TB.FALSE(services));
//        
//        //"C.<classInitializationInProgress> = FALSE"
//        Term notInitInProgress
//            = TB.equals(TB.dotClassInitializationInProgress(services,  
//        	                                            classKJT.getSort()), 
//        	        TB.FALSE(services));
//        
//        return TB.and(notErroneous, notInitInProgress);
//    }
    
    
    /**
     * Builds the "general assumption" for a set of assumed invariants. 
     */
    private Term buildFreePre(ProgramVariable selfVar,
                              ImmutableList<ProgramVariable> paramVars) 
    		throws ProofInputException {

        //"self != null"
        Term selfNotNull 
            = selfVar == null
              ? TB.tt()
              : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
        	      
        //"self.<created> = TRUE"
        Term selfCreated
           = selfVar == null
             ? TB.tt()
             : TB.equals(TB.dotCreated(services, 
                                       TB.var(selfVar)), 
                         TB.TRUE(services));
        
        //conjunction of... 
        //- "p_i.<created> = TRUE | p_i = null" for object parameters, and
        //- "inBounds(p_i)" for integer parameters
        Term paramsOK = TB.tt();
        for(ProgramVariable paramVar : paramVars) {
            paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
        }

        return TB.and(new Term[]{TB.inReachableState(services), 
        	       		 selfNotNull,
        	       		 selfCreated,
        	       		 paramsOK});
    }
    
    
    private JavaBlock buildJavaBlock(
	    			ImmutableList<LocationVariable> formalParVars,
                                ProgramVariable selfVar, 
                                ProgramVariable resultVar,
                                ProgramVariable exceptionVar) {        
        //create method call
	final ImmutableArray<Expression> formalArray 
		= new ImmutableArray<Expression>(formalParVars.toArray(
			            new ProgramVariable[formalParVars.size()]));
	final MethodBodyStatement call 
		= new MethodBodyStatement(contract.getProgramMethod(),
					  selfVar,
					  resultVar,
					  formalArray);
	final StatementBlock sb = new StatementBlock(call);
        
        //create variables for try statement
        final KeYJavaType eType 
        	= javaInfo.getTypeByClassName("java.lang.Throwable");
        final TypeReference excTypeRef = javaInfo.createTypeReference(eType);
        final ProgramElementName ePEN = new ProgramElementName("e");
        final ProgramVariable eVar = new LocationVariable (ePEN, eType);
        
        //create try statement
        final CopyAssignment nullStat = new CopyAssignment(exceptionVar, 
                                                           NullLiteral.NULL);
        final VariableSpecification eSpec = new VariableSpecification(eVar);
        final ParameterDeclaration excDecl 
        	= new ParameterDeclaration(new Modifier[0],
        				   excTypeRef,
        				   eSpec,
        				   false);
        final CopyAssignment assignStat = new CopyAssignment(exceptionVar, eVar);
        final Catch catchStat = new Catch(excDecl, new StatementBlock(assignStat));
        final Try tryStat = new Try(sb, new Branch[]{catchStat});
        final StatementBlock sb2 = new StatementBlock(new Statement[]{nullStat, 
        							      tryStat});
                
        //create java block
        JavaBlock result = JavaBlock.createJavaBlock(sb2);
        
        return result;
    }
    
    
    private Term buildProgramTerm(ImmutableList<ProgramVariable> paramVars,
                                  ProgramVariable selfVar, 
                                  ProgramVariable resultVar,
                                  ProgramVariable exceptionVar,
                                  LocationVariable heapAtPreVar,
                                  Term postTerm) {
        //create formal parameters
        ImmutableList<LocationVariable> formalParamVars 
        	= ImmutableSLList.<LocationVariable>nil();
        for(ProgramVariable paramVar : paramVars) {
            ProgramElementName pen 
                = new ProgramElementName("_" + paramVar.name());            
            LocationVariable formalParamVar
            	= new LocationVariable(pen, paramVar.getKeYJavaType());
            formalParamVars = formalParamVars.append(formalParamVar);
        }
        
        //create java block
        final JavaBlock jb = buildJavaBlock(formalParamVars,
                                            selfVar,
                                            resultVar,
                                            exceptionVar);
        
        //create program term
        final Term programTerm = TB.mod(contract.getModality(), jb, postTerm);
        
        //create update
        Term update = TB.elementary(services, heapAtPreVar, TB.heap(services));
        Iterator<LocationVariable> formalParamIt = formalParamVars.iterator();
        Iterator<ProgramVariable> paramIt        = paramVars.iterator();
        while(formalParamIt.hasNext()) {
            Term paramUpdate = TB.elementary(services, 
        	    			     formalParamIt.next(), 
        	    			     TB.var(paramIt.next()));
            update = TB.parallel(update, paramUpdate);
        }
        
        return TB.apply(update, programTerm);
    }
           
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------        
    
    @Override
    public void readProblem() throws ProofInputException {
	final ProgramMethod pm = contract.getProgramMethod();
	
        //prepare variables, program method, heapAtPre
        final ImmutableList<ProgramVariable> paramVars = buildParamVars(pm);
        final ProgramVariable selfVar
            = pm.isStatic() ? null : buildSelfVarAsProgVar();
        final ProgramVariable resultVar = buildResultVar(pm);
        final ProgramVariable exceptionVar = buildExcVar();
     	final LocationVariable heapAtPreVar 
		= new LocationVariable(new ProgramElementName("heapAtPre"),
				       new KeYJavaType(heapLDT.targetSort()));
        final Term heapAtPre = TB.var(heapAtPreVar);

        //build precondition
        final Term pre = TB.and(buildFreePre(selfVar, paramVars), 
        	                contract.getPre(selfVar, paramVars, services)); 
                
        //build program term
        final Term post = TB.and(contract.getPost(selfVar, 
                                    	   	  paramVars, 
                                    	   	  resultVar, 
                                    	   	  exceptionVar,
                                    	   	  heapAtPre,
                                    	   	  services),
                                 TB.frame(services, 
                                	  heapAtPre, 
                                	  contract.getModifies(selfVar, 
                                		  	       paramVars, 
                                		  	       services)));
        final Term progPost = buildProgramTerm(paramVars,
                                               selfVar,
                                               resultVar,
                                               exceptionVar,
                                               heapAtPreVar,
                                               post);
        
        //save in field
        poTerms = new Term[]{TB.imp(pre, progPost)};
    }
    
    
    public OperationContract getContract() {
        return contract;
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        if(!(po instanceof ContractPO)) {
            return false;
        }
        ContractPO cPO = (ContractPO) po;
        return specRepos.splitContract(cPO.contract)
                        .subset(specRepos.splitContract(contract));
    }
    
    
    @Override
    public boolean equals(Object o) {
	if(!(o instanceof ContractPO)) {
	    return false;
	} else {
	    return contract.equals(((ContractPO)o).contract);
	}
    }
    
    
    @Override
    public int hashCode() {
        return contract.hashCode();
    }
}
