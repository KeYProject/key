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

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

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
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.OperationContract;


/**
 * The proof obligation for operation contracts. 
 */
public final class OperationContractPO extends AbstractPO 
                                       implements ContractPO {
    
    private final OperationContract contract;
    private Term mbyAtPre;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public OperationContractPO(InitConfig initConfig, 
	    		       OperationContract contract) {
    	super(initConfig, contract.getName());
    	this.contract = contract;
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------    
    
    /**
     * Builds the "general assumption". 
     */
    private Term buildFreePre(ProgramVariable selfVar,
	                      KeYJavaType selfKJT,
                              ImmutableList<ProgramVariable> paramVars) 
    		throws ProofInputException {
        //"self != null"
        final Term selfNotNull 
            = selfVar == null || contract.getTarget().isConstructor()
              ? TB.tt()
              : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
        	      
        //"self.<created> = TRUE"
        final Term selfCreated
           = selfVar == null || contract.getTarget().isConstructor()
             ? TB.tt()
             : TB.created(services, TB.var(selfVar));
             
        //"MyClass::exactInstance(self) = TRUE"
        final Term selfExactType
           = selfVar == null || contract.getTarget().isConstructor()
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
        
        //initial value of measured_by clause
        final Term mbyAtPreDef;
        if(contract.hasMby()) {
            final Function mbyAtPreFunc
            	= new Function(new Name(TB.newName(services, "mbyAtPre")), 
        		       services.getTypeConverter()
        		               .getIntegerLDT()
        		               .targetSort());
            mbyAtPre = TB.func(mbyAtPreFunc);
            final Term mby = contract.getMby(selfVar, paramVars, services);
            mbyAtPreDef = TB.equals(mbyAtPre, mby);
        } else {
            mbyAtPreDef = TB.tt();
        }

        return TB.and(new Term[]{TB.wellFormedHeap(services), 
        	       		 selfNotNull,
        	       		 selfCreated,
        	       		 selfExactType,
        	       		 paramsOK,
        	       		 mbyAtPreDef});
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
	final StatementBlock sb;
	if(contract.getTarget().isConstructor()) {
	    assert selfVar != null;
	    assert resultVar == null;
	    final Expression[] formalArray2 
	    	= formalArray.toArray(new Expression[formalArray.size()]);
	    final New n 
	    	= new New(formalArray2, new TypeRef(contract.getKJT()), null);
	    final CopyAssignment ca = new CopyAssignment(selfVar, n);
	    sb = new StatementBlock(ca);
	} else {
	    final MethodBodyStatement call 
		= new MethodBodyStatement(contract.getTarget(),
					  selfVar,
					  resultVar,
					  formalArray);
	    sb = new StatementBlock(call);
	}

        //create variables for try statement
        final KeYJavaType eType 
        	= javaInfo.getTypeByClassName("java.lang.Exception");
        final TypeReference excTypeRef = javaInfo.createTypeReference(eType);
        final ProgramElementName ePEN = new ProgramElementName("e");
        final ProgramVariable eVar = new LocationVariable(ePEN, eType);
        
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
            register(formalParamVar);
        }
        
        //create java block
        final JavaBlock jb = buildJavaBlock(formalParamVars,
                                            selfVar,
                                            resultVar,
                                            exceptionVar);
        
        //create program term
        final Term programTerm = TB.prog(contract.getModality(), jb, postTerm);
        
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
	final ProgramMethod pm = contract.getTarget();
	
        //prepare variables, program method, heapAtPre
        final ImmutableList<ProgramVariable> paramVars 
        	= TB.paramVars(services, pm, true);
        final ProgramVariable selfVar 
        	= TB.selfVar(services, pm, contract.getKJT(), true);
        final ProgramVariable resultVar = TB.resultVar(services, pm, true);
        final ProgramVariable exceptionVar = TB.excVar(services, pm, true);
     	final LocationVariable heapAtPreVar 
		= TB.heapAtPreVar(services, "heapAtPre", true);
        final Term heapAtPre = TB.var(heapAtPreVar);
        final Map<Term,Term> normalToAtPre = new HashMap<Term,Term>();
        normalToAtPre.put(TB.heap(services), heapAtPre);
        
        //register the variables so they are declared in proof header 
        //if the proof is saved to a file
        register(paramVars);
        register(selfVar);
        register(resultVar);
        register(exceptionVar);
        register(heapAtPreVar);

        //build precondition
        final Term pre = TB.and(buildFreePre(selfVar, 
        	                             contract.getKJT(), 
        	                             paramVars), 
        	                contract.getPre(selfVar, paramVars, services));
                
        //build program term
        final Term post = TB.and(contract.getPost(selfVar, 
                                    	   	  paramVars, 
                                    	   	  resultVar, 
                                    	   	  exceptionVar,
                                    	   	  heapAtPre,
                                    	   	  services),
                                 TB.frame(services, 
                                	  normalToAtPre, 
                                	  contract.getMod(selfVar, 
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
        
        //add axioms
        collectClassAxioms(contract.getKJT());
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        if(!(po instanceof OperationContractPO)) {
            return false;
        }
        OperationContractPO cPO = (OperationContractPO) po;
        return specRepos.splitContract(cPO.contract)
                        .subset(specRepos.splitContract(contract));
    }
    
    
    @Override
    public OperationContract getContract() {
        return contract;
    }
    
    
    @Override
    public Term getMbyAtPre() {
	return mbyAtPre;
    }
    
    
    @Override
    public boolean equals(Object o) {
	if(!(o instanceof OperationContractPO)) {
	    return false;
	} else {
	    return contract.equals(((OperationContractPO)o).contract);
	}
    }
    
    
    @Override
    public int hashCode() {
        return contract.hashCode();
    }
}
