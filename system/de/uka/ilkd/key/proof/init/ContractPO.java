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
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.OperationContract;


/**
 * The "Ensures" proof obligation. 
 */
public final class ContractPO extends AbstractPO {
    
    private final OperationContract contract;
    
    private ImmutableSet<NoPosTacletApp> taclets 
    	= DefaultImmutableSet.<NoPosTacletApp>nil();
       
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public ContractPO(InitConfig initConfig, OperationContract contract) {
    	super(initConfig, contract.getName());
    	this.contract = contract;
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    
    private Taclet buildAxiomTaclet(ClassAxiom ax, 
	    			    ProgramVariable selfVar) {
	final Term axiomTerm = ax.getAxiom(selfVar, services);
	if(!(axiomTerm.op() instanceof Equality)) {
	    return null;
	}
	final Term lhs = axiomTerm.sub(0);
	final Term rhs = axiomTerm.sub(1);
	
	final SchemaVariable heapSV 
		= SchemaVariableFactory.createTermSV(new Name("h"), 
						     heapLDT.targetSort(), 
						     false, 
						     false);
	final Map map = new HashMap();
	map.put(TB.heap(services), TB.var(heapSV));
	final OpReplacer or = new OpReplacer(map);
	final Term schemaLhs = or.replace(lhs);
	final Term schemaRhs = or.replace(rhs);
	
	RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
	tacletBuilder.setFind(schemaLhs);
	tacletBuilder.addTacletGoalTemplate
	    (new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
					   ImmutableSLList.<Taclet>nil(),
					   schemaRhs));
	tacletBuilder.setName(new Name(ax.getName()));
	tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));
	
	return tacletBuilder.getTaclet();
    }
    
    
    /**
     * Builds the "general assumption". 
     */
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
            Taclet axiomTaclet = buildAxiomTaclet(ax, selfVar);
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
        
        return TB.and(new Term[]{TB.inReachableState(services), 
        	       		 selfNotNull,
        	       		 selfCreated,
        	       		 selfExactType,
        	       		 paramsOK,
        	       		 axiomTerm});
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
	final ProgramMethod pm = contract.getProgramMethod();
	
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
        poTaclets = new ImmutableSet[]{taclets};        
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
