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

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.ArrayOfExpression;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.ldt.AbstractIntegerLDT;
import de.uka.ilkd.key.logic.ldt.LDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.proof.mgt.OldOperationContract;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.Debug;


/**
 * The "Ensures" proof obligation. 
 */
public abstract class EnsuresPO extends AbstractPO {

    public final ModelMethod modelMethod;
    public final Modality modality;
    private final InvariantSelectionStrategy invStrategy;
    private final boolean skipPreconditions;
    
    private SetOfTaclet invTaclets = SetAsListOfTaclet.EMPTY_SET;

    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public EnsuresPO(String name,
		     ModelMethod modelMethod,
		     Modality modality,
                     InvariantSelectionStrategy invStrategy,
                     boolean skipPreconditions) {
    	super(name + " of " + modelMethod, 
              modelMethod.getContainingClass());
    	this.modelMethod       = modelMethod;
    	this.modality          = modality; 
        this.invStrategy       = invStrategy;
        this.skipPreconditions = skipPreconditions;
    }
    
    
    
    //-------------------------------------------------------------------------
    //template methods to be implemented by subclasses
    //-------------------------------------------------------------------------
  
    protected abstract Term getPreTerm(ProgramVariable selfVar, 
                                       ListOfProgramVariable paramVars, 
                                       ProgramVariable resultVar,
                                       ProgramVariable exceptionVar,
                                       Map atPreFunctions) 
                                                    throws ProofInputException, SLTranslationError;
    
    
    protected abstract Term getPostTerm(ProgramVariable selfVar, 
                                        ListOfProgramVariable paramVars, 
                                        ProgramVariable resultVar,
                                        ProgramVariable exceptionVar,
                                        Map atPreFunctions)
                                                    throws ProofInputException, SLTranslationError;
    

 
    
    //-------------------------------------------------------------------------
    //local helper methods
    //-------------------------------------------------------------------------    
    
    /**
     * Returns the program method associated with this proof obligation.
     */
    private ProgramMethod getProgramMethod(ListOfProgramVariable paramVars) {
        //get class type
        String className = modelClass.getFullClassName();
        KeYJavaType classType = javaInfo.getTypeByClassName(className); 
        Debug.assertTrue(classType != null);
                
        //get program method
        return javaInfo.getProgramMethod(classType, 
                                         modelMethod.getName(), 
                                         paramVars.toArray(), 
                                         classType);
    }
    

    /**
     * (helper for buildAssumedInvs())
     * @throws SLTranslationError 
     * @throws ProofInputException 
     */
    private Term buildInvariantsForClass(ModelClass modelClass) throws SLTranslationError  {
        String className = modelClass.getFullClassName();
        KeYJavaType classType = javaInfo.getTypeByClassName(className);
        
        //add "C.<classErroneous> = FALSE"
        ProgramVariable erroneousField 
            = javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_ERRONEOUS, 
                                    classType);
        Term result = tb.equals(tb.var(erroneousField), tb.FALSE(services)); 
        
        //add "C.<classInitialisationInProgress> = FALSE"
        ProgramVariable initField 
            = javaInfo.getAttribute(
                        ImplicitFieldAdder.IMPLICIT_CLASS_INIT_IN_PROGRESS, 
                        classType);
        Term initFalseTerm = tb.equals(tb.var(initField), tb.FALSE(services));
        result = tb.and(result, initFalseTerm);
        
        //add explicit invariants
        ListOfClassInvariant invs = modelClass.getMyClassInvariants();
        invs = invs.append(modelClass.getMyThroughoutClassInvariants());
    	Term invTerm = translateInvs(invs);
    	result = tb.and(result, invTerm);

        return result;
    }
    
    
    /**
     * (helper for buildAssumedInvs())
     * @throws SLTranslationError 
     */
    private void buildInvariantTacletsForClass(ModelClass modelClass) throws SLTranslationError {
        Term invTerm = buildInvariantsForClass(modelClass);
        ConstrainedFormula cf = new ConstrainedFormula(invTerm);
        Semisequent ante 
            = Semisequent.EMPTY_SEMISEQUENT.insertLast(cf).semisequent();
        Sequent sequent = Sequent.createAnteSequent(ante);
        
        TacletGoalTemplate template 
            = new TacletGoalTemplate(sequent, 
                                     SLListOfTaclet.EMPTY_LIST);
        
        NoFindTacletBuilder tacletBuilder = new NoFindTacletBuilder();
        String name = "Insert invariants of " + modelClass.getClassName();
        tacletBuilder.setName(new Name(name));
        tacletBuilder.addTacletGoalTemplate(template);
        Taclet taclet = tacletBuilder.getNoFindTaclet();
        invTaclets = invTaclets.add(taclet);
        initConfig.getProofEnv().registerRule(taclet, 
                                              AxiomJustification.INSTANCE);
    }
    
    
    private Term buildAssumedInvs() throws SLTranslationError {
        Debug.assertTrue(invStrategy != null);
        String ownFullName    = modelClass.getFullClassName();
        String ownPackageName = modelClass.getContainingPackage();
        if(ownPackageName == null) {
            ownPackageName = "";
        }
        
        //inReachableState
        Term result = tb.func(javaInfo.getInReachableState());
        
        //collect all translated invariants of all classes
        Set allClasses = modelClass.getAllClasses();
        Iterator it = allClasses.iterator();
        while(it.hasNext()) {
            ModelClass mc = (ModelClass)(it.next());

            //display only those designated by the invariant display strategy
            if(invStrategy.preselectAll()
               || (invStrategy.preselectPackage()
                    && ownPackageName.equals(mc.getContainingPackage())) 
               || (invStrategy.preselectClass() 
                    && ownFullName.equals(mc.getFullClassName()))) {
                Term classInvTerm = buildInvariantsForClass(mc);
                result = tb.and(result, classInvTerm);
            } else {
                buildInvariantTacletsForClass(mc);
            }
        }
        
        return result;
    }
    
    
    /**
     * Builds the "general assumption" for a set of assumed invariants.
     * @throws SLTranslationError 
     */
    private Term buildGeneralAssumption(ProgramVariable selfVar,
                                        ListOfProgramVariable paramVars) throws SLTranslationError {
        Term result = null;
        
        //build conjunction of invariants
        Term assumedInvsTerm = buildAssumedInvs();
        result = assumedInvsTerm;
        
        //build disjunction of preconditions
        if(!skipPreconditions) {
            Term anyPreTerm = tb.ff();
            ListOfOperationContract contracts 
                = modelMethod.getMyOperationContracts();
            IteratorOfOperationContract it = contracts.iterator();
            while(it.hasNext()) {
                OperationContract contract = it.next();
                Term term = translatePre(contract, selfVar, toPV(paramVars));
                anyPreTerm = tb.or(anyPreTerm, term); 
            }
            result = tb.and(result, anyPreTerm);
        }
        
        //build "self.<created> = TRUE & self != null"
        if(selfVar != null) {
            Term selfCreatedAndNotNullTerm
                = createdFactory.createCreatedAndNotNullTerm(services,
                                                             tb.var(selfVar));
            result = tb.and(result, selfCreatedAndNotNullTerm);
        }
        
        //build conjunction of... 
        //- "p_i.<created> = TRUE | p_i = null" for object parameters, and
        //- "inBounds(p_i)" for integer parameters
        Term paramsLegalTerm = tb.tt();
        IteratorOfProgramVariable it2 = paramVars.iterator();
        while(it2.hasNext()) {
            ProgramVariable paramVar = it2.next();
            Term paramLegalTerm = tb.tt();
            if(paramVar.sort() instanceof ObjectSort) {
                paramLegalTerm
                    = createdFactory.createCreatedOrNullTerm(services, 
                                                             tb.var(paramVar)); 
            } else {
        	LDT ldt 
        	    = services.getTypeConverter().getModelFor(paramVar.sort());
        	if(ldt instanceof AbstractIntegerLDT) {
        	    Function inBoundsPredicate 
        	    	= ((AbstractIntegerLDT)ldt).getInBoundsPredicate();
        	    if(inBoundsPredicate != null) {
        		paramLegalTerm = tb.func(inBoundsPredicate, 
        					 tb.var(paramVar));
        	    }
        	}
            }
            paramsLegalTerm = tb.and(paramsLegalTerm, paramLegalTerm);
        }
        result = tb.and(result, paramsLegalTerm);
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
            ProgramElementName name 
                    = new ProgramElementName("_" + parVars[i].name());
            formalParVars[i] 
                    = new LocationVariable(name, parVars[i].getKeYJavaType());
            registerInNamespaces(formalParVars[i]);
        }
        
        //create java block
        JavaBlock jb = buildJavaBlock(formalParVars,
                                      programMethod,
                                      selfVar,
                                      resultVar,
                                      exceptionVar);
        
        //create program term
        Term programTerm = tf.createProgramTerm(modality, jb, postTerm);
        
        //add updates
        Term[] locs   = new Term[parVars.length];
        Term[] values = new Term[parVars.length];
        for(int i = 0; i < parVars.length; i++) {
            locs[i]   = tb.var(formalParVars[i]);
            values[i] = tb.var(parVars[i]);
        }
        Term updateTerm = tf.createUpdateTerm(locs, values, programTerm);
        
        return updateTerm;
    }
    
    
    
    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------        
    
    public void readProblem(ModStrategy mod) throws ProofInputException {
        //make sure initConfig has been set
        if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
        
        //prepare variables, program method and container for @pre-functions
        ListOfProgramVariable paramVars = buildParamVars(modelMethod);
        ProgramMethod programMethod = getProgramMethod(paramVars);
        ProgramVariable selfVar = null;
        if(programMethod != null && !programMethod.isStatic()) {
            selfVar = buildSelfVarAsProgVar();
        }
        ProgramVariable resultVar = buildResultVar(modelMethod);
        ProgramVariable exceptionVar = buildExcVar();
        Map atPreFunctions = new HashMap();
        
        try {
        	//build general assumption
	        Term gaTerm = buildGeneralAssumption(selfVar, paramVars);
	        
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
	        Term atPreDefinitionsTerm = buildAtPreDefinitions(atPreFunctions);
	        
	        //put everything together
	        Term result = tb.and(atPreDefinitionsTerm, gaTerm);
	        result = tb.and(result, preTerm);
	        result = tb.imp(result, programTerm);
	        
	
	        //save in field
	        poTerms = new Term[]{result};
	        poTaclets = new SetOfTaclet[]{invTaclets};
	        
        } catch (SLTranslationError e) {
            throw new ProofInputException(e);
        }

        //register everything in namespaces
        registerInNamespaces(selfVar);
        registerInNamespaces(paramVars);
        registerInNamespaces(resultVar);
        registerInNamespaces(exceptionVar);
        registerInNamespaces(atPreFunctions);
    }


    public Contractable[] getObjectOfContract() {
        return new Contractable[] { modelMethod };
    }

    
    public boolean initContract(Contract ct) {
        if(!(ct instanceof OldOperationContract)) {
            return false;
        }
        
        OldOperationContract mct = (OldOperationContract)ct;
        
        if(! (mct.getModelMethod().equals(modelMethod)
                && mct.getModality().equals(modality))) {
            return false;
        }
        
        ct.addCompoundProof(getPO());
        return true;
    }
}
