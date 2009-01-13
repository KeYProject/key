// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.*;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.ldt.AbstractIntegerLDT;
import de.uka.ilkd.key.logic.ldt.LDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.*;


/**
 * The "Ensures" proof obligation. 
 */
public abstract class EnsuresPO extends AbstractPO {
    
    private final ProgramMethod programMethod;
    private final Modality modality;
    private final SetOfClassInvariant assumedInvs;
    
    private final boolean skipPreconditions;
    
    private SetOfTaclet invTaclets = SetAsListOfTaclet.EMPTY_SET;

    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public EnsuresPO(InitConfig initConfig,
	    	     String name,
		     ProgramMethod programMethod,
		     Modality modality,
                     SetOfClassInvariant assumedInvs,
                     boolean skipPreconditions) {
    	super(initConfig, 
    	      name + " of " + programMethod, 
    	      programMethod.getContainerType());
    	this.programMethod     = programMethod;
    	this.modality          = modality; 
        this.assumedInvs       = assumedInvs;
        this.skipPreconditions = skipPreconditions;
    }
    
    
    
    //-------------------------------------------------------------------------
    //template methods to be implemented by subclasses
    //-------------------------------------------------------------------------
  
    protected abstract Term getPreTerm(ProgramVariable selfVar, 
                                       ListOfProgramVariable paramVars, 
                                       ProgramVariable resultVar,
                                       ProgramVariable exceptionVar,
                                       Map<Operator, Function/*atPre*/> atPreFunctions) 
                                                    throws ProofInputException;
    
    
    protected abstract Term getPostTerm(ProgramVariable selfVar, 
                                        ListOfProgramVariable paramVars, 
                                        ProgramVariable resultVar,
                                        ProgramVariable exceptionVar,
                                        Map<Operator, Function/*atPre*/> atPreFunctions)
                                                    throws ProofInputException;
    

 
    
    //-------------------------------------------------------------------------
    //local helper methods
    //-------------------------------------------------------------------------    

    /**
     * (helper for buildAssumedInvs())
     */
    private Term buildImplicitInvariantsForClass(KeYJavaType classKJT) 
    		throws ProofInputException {
	assert classKJT.getJavaType() instanceof ClassType;
	Term result = TB.tt();
	
        //add "C.<classErroneous> = FALSE"
        ProgramVariable erroneousField 
            = javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_ERRONEOUS, 
                                    classKJT);
        if(erroneousField != null) {
            result = TB.and(result, 
        	    	    TB.equals(TB.var(erroneousField), 
        	    		      TB.FALSE(services)));
        }
        
        //add "C.<classInitialisationInProgress> = FALSE"
        ProgramVariable initField 
            = javaInfo.getAttribute(
                        ImplicitFieldAdder.IMPLICIT_CLASS_INIT_IN_PROGRESS, 
                        classKJT);
        if(initField != null) {
            Term initFalseTerm = TB.equals(TB.var(initField), TB.FALSE(services));
            result = TB.and(result, initFalseTerm);
        }
        
        return result;
    }
    
    
    /**
     * (helper for buildAssumedInvs()) 
     */
    private void buildInvariantTacletsForClass(KeYJavaType classKJT) 
    		throws ProofInputException {
	assert classKJT.getJavaType() instanceof ClassType;
	
        Term invTerm = buildImplicitInvariantsForClass(classKJT);
        ConstrainedFormula cf = new ConstrainedFormula(invTerm);
        Semisequent ante 
            = Semisequent.EMPTY_SEMISEQUENT.insertLast(cf).semisequent();
        Sequent sequent = Sequent.createAnteSequent(ante);
        
        TacletGoalTemplate template 
            = new TacletGoalTemplate(sequent, 
                                     SLListOfTaclet.EMPTY_LIST);
        
        NoFindTacletBuilder tacletBuilder = new NoFindTacletBuilder();
        String s = "Insert implicit invariants of " + classKJT.getName();
        tacletBuilder.setName(new Name(s));
        tacletBuilder.addTacletGoalTemplate(template);
        Taclet taclet = tacletBuilder.getNoFindTaclet();
        invTaclets = invTaclets.add(taclet);
        initConfig.getProofEnv().registerRule(taclet, 
                                              AxiomJustification.INSTANCE);
    }
    
    
    private Term buildAssumedInvs() throws ProofInputException {
        //inReachableState
        Term result = TB.func(javaInfo.getInReachableState());
        
        //assumed invariants
        final IteratorOfClassInvariant it = assumedInvs.iterator();
        while(it.hasNext()) {
            result = TB.and(result, translateInv(it.next()));
        }
        
        //implicit invariants as taclets
        final Iterator<KeYJavaType> it2 = javaInfo.getAllKeYJavaTypes().iterator();
        while(it2.hasNext()) {
            KeYJavaType kjt = it2.next();
            if(kjt.getJavaType() instanceof ClassType) {
                buildInvariantTacletsForClass(kjt);
            }
        }
        
        return result;
    }
  
    /**
     * Builds the "general assumption" about the amount of available memory. 
     */
    protected Term buildGeneralMemoryAssumption(ProgramVariable selfVar,
                                        ListOfProgramVariable paramVars) 
                throws ProofInputException {
        return TB.tt();
    }
    
    /**
     * Builds the "general assumption" for a set of assumed invariants. 
     */
    private Term buildGeneralAssumption(ProgramVariable selfVar,
                                        ListOfProgramVariable paramVars) 
    		throws ProofInputException {
        Term result = null;
        
        //build conjunction of invariants
        Term assumedInvsTerm = buildAssumedInvs();
        result = assumedInvsTerm;
        
        //build disjunction of preconditions
        if(!skipPreconditions) {
            Term anyPreTerm = TB.ff();
            SetOfOperationContract contracts 
                = specRepos.getOperationContracts(programMethod);
            IteratorOfOperationContract it = contracts.iterator();
            while(it.hasNext()) {
                OperationContract contract = it.next();
                Term term = translatePre(contract, selfVar, toPV(paramVars));
                anyPreTerm = TB.or(anyPreTerm, term); 
            }
            result = TB.and(result, anyPreTerm);
        }
        
        //build "self.<created> = TRUE & self != null"
        if(selfVar != null) {
            Term selfCreatedAndNotNullTerm
                = createdFactory.createCreatedAndNotNullTerm(services,
                                                             TB.var(selfVar));
            result = TB.and(result, selfCreatedAndNotNullTerm);
        }
        
        //build conjunction of... 
        //- "p_i.<created> = TRUE | p_i = null" for object parameters, and
        //- "inBounds(p_i)" for integer parameters
        Term paramsLegalTerm = TB.tt();
        IteratorOfProgramVariable it2 = paramVars.iterator();
        while(it2.hasNext()) {
            ProgramVariable paramVar = it2.next();
            Term paramLegalTerm = TB.tt();
            if(paramVar.sort() instanceof ObjectSort) {
                paramLegalTerm
                    = createdFactory.createCreatedOrNullTerm(services, 
                                                             TB.var(paramVar)); 
            } else {
                Type paramType = paramVar.getKeYJavaType().getJavaType();
                LDT ldt = services.getTypeConverter().getModelFor(paramType);
                
                if(ldt instanceof AbstractIntegerLDT) {
                    Function inBoundsPred 
                        = ((AbstractIntegerLDT) ldt).getInBounds();
                    paramLegalTerm = TB.func(inBoundsPred, TB.var(paramVar));
                }
            }
            paramsLegalTerm = TB.and(paramsLegalTerm, paramLegalTerm);
        }
        result = TB.and(result, paramsLegalTerm);
        
        return result;        
    }
    
    
    private JavaBlock buildJavaBlock(ProgramVariable[] formalParVars,
                                     ProgramMethod programMethod, 
                                     ProgramVariable selfVar, 
                                     ProgramVariable resultVar,
                                     ProgramVariable exceptionVar) {        
        //create method call
	StatementBlock sb;
	if(programMethod == null) {
	    //constructor
	    assert resultVar != null;
	    TypeReference typeRef 
	    	= javaInfo.createTypeReference(resultVar.getKeYJavaType());
	    New n = new New(formalParVars, typeRef, typeRef);
	    CopyAssignment copy = new CopyAssignment(resultVar, n);
	    sb = new StatementBlock(copy);
	} else {
	    MethodBodyStatement call 
            	= new MethodBodyStatement(programMethod,
            				  selfVar,
            				  resultVar,
            				  new ArrayOfExpression(formalParVars));
	    sb = new StatementBlock(call);
	}
        
        //create variables for try statement
        KeYJavaType eType = javaInfo.getTypeByClassName("java.lang.Throwable");
        TypeReference excTypeRef = javaInfo.createTypeReference(eType);
        ProgramElementName ePEN = new ProgramElementName("e");
        ProgramVariable eVar = new LocationVariable (ePEN, eType);
        
        //create try statement
        CopyAssignment nullStat = new CopyAssignment(exceptionVar, 
                                                     NullLiteral.NULL);
        VariableSpecification eSpec = new VariableSpecification(eVar);
        ParameterDeclaration excDecl = new ParameterDeclaration(new Modifier[0],
                                                                excTypeRef,
                                                                eSpec,
                                                                false);
        CopyAssignment assignStat = new CopyAssignment(exceptionVar, eVar);
        Catch catchStat = new Catch(excDecl, new StatementBlock(assignStat));
        Try tryStat = new Try(sb, new Branch[]{catchStat});
        sb = new StatementBlock(new Statement[]{nullStat, tryStat});
        if(ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof PercProfile){
            sb = new StatementBlock(new MethodFrame(null, 
                    services.getJavaInfo().getDefaultExecutionContext(), sb));
        }
        //create java block
        JavaBlock result = JavaBlock.createJavaBlock(sb);
        
        return result;
    }
    
    
    private Term buildProgramTerm(ProgramVariable[] parVars,
                                  ProgramMethod programMethod, 
                                  ProgramVariable selfVar, 
                                  ProgramVariable resultVar,
                                  ProgramVariable exceptionVar,
                                  Term postTerm) {
        //create formal parameters
        ProgramVariable[] formalParVars = new ProgramVariable[parVars.length];
        for(int i = 0; i < parVars.length; i++) {
            ProgramElementName pen 
                    = new ProgramElementName("_" + parVars[i].name());
            formalParVars[i] 
                    = new LocationVariable(pen, parVars[i].getKeYJavaType());
            registerInNamespaces(formalParVars[i]);
        }
        
        //create java block
        JavaBlock jb = buildJavaBlock(formalParVars,
                                      programMethod,
                                      selfVar,
                                      resultVar,
                                      exceptionVar);
        
        //create program term
        Term programTerm = TF.createProgramTerm(modality, jb, postTerm);
        
        //add updates
        Term[] locs   = new Term[parVars.length];
        Term[] values = new Term[parVars.length];
        for(int i = 0; i < parVars.length; i++) {
            locs[i]   = TB.var(formalParVars[i]);
            values[i] = TB.var(parVars[i]);
        }
        Term updateTerm = TF.createUpdateTerm(locs, values, programTerm);
        
        return updateTerm;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------        
    
    public void readProblem(ModStrategy mod) throws ProofInputException {
        //prepare variables, program method and container for @pre-functions
        ListOfProgramVariable paramVars = buildParamVars(programMethod);
        ProgramVariable selfVar = null;
        if(programMethod != null && !programMethod.isStatic()) {
            selfVar = buildSelfVarAsProgVar();
        }
        ProgramVariable resultVar = buildResultVar(programMethod);
        ProgramVariable exceptionVar = buildExcVar();
        Map<Operator, Function/*atPre*/> atPreFunctions = 
            new LinkedHashMap<Operator, Function/*atPre*/>();
        
        //build general assumption
        Term gaTerm = buildGeneralAssumption(selfVar, paramVars);
        
        Term gaMTerm = buildGeneralMemoryAssumption(selfVar, paramVars);
        
        //get precondition defined by subclass
        Term preTerm = getPreTerm(selfVar, 
                                  paramVars, 
                                  resultVar, 
                                  exceptionVar, 
                                  atPreFunctions);
        
        //get postcondition defined by subclass
        Term postTerm = getPostTerm(selfVar, 
                                    paramVars, 
                                    resultVar, 
                                    exceptionVar, 
                                    atPreFunctions);
        
        //build program term
        Term programTerm = buildProgramTerm(paramVars.toArray(),
                                            programMethod,
                                            selfVar,
                                            resultVar,
                                            exceptionVar,
                                            postTerm);
        
        //build definitions for @pre-functions
        Update atPreDefinitions = APF.createAtPreDefinitions(atPreFunctions, 
                                                             services);
        
        //put everything together
        Term result = TB.imp(TB.and(TB.and(gaTerm, gaMTerm), uf.apply(atPreDefinitions, preTerm)), 
                             uf.apply(atPreDefinitions, programTerm));
        
        //save in field
        poTerms = new Term[]{result};
        poTaclets = new SetOfTaclet[]{invTaclets};
        
        //register everything in namespaces
        registerInNamespaces(selfVar);
        registerInNamespaces(paramVars);
        registerInNamespaces(resultVar);
        registerInNamespaces(exceptionVar);
        registerInNamespaces(atPreFunctions);
    }
    
    
    public ProgramMethod getProgramMethod() {
        return programMethod;
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof EnsuresPO)) {
            return false;
        }
        EnsuresPO po = (EnsuresPO) o;
        return programMethod.equals(po.programMethod)
               && modality.equals(po.modality)
               && assumedInvs.equals(po.assumedInvs);
    }
    
    
    public int hashCode() {
        return programMethod.hashCode() 
               + modality.hashCode() 
               + assumedInvs.hashCode();
    }
}
