// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.*;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.casetool.UMLModelClass;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.SetOfTaclet;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.speclang.*;



/**
 * An abstract proof obligation implementing common functionality.
 */
public abstract class AbstractPO implements ProofOblInput {

    protected static final TermFactory tf = TermFactory.DEFAULT;
    protected static final CreatedAttributeTermFactory createdFactory
                                   = CreatedAttributeTermFactory.INSTANCE;
    protected static final TermBuilder tb = TermBuilder.DF;
    
    private final String name;
    protected final ModelClass modelClass;

    protected InitConfig initConfig = null;
    protected Services services     = null;
    protected JavaInfo javaInfo     = null;

    private Map /*Operator -> Term*/ axioms = new HashMap();
    private String header = null;
    private ProofAggregate proofAggregate = null;
    
    protected Term[] poTerms          = null;
    protected String[] poNames        = null;
    protected SetOfTaclet[] poTaclets = null;

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public AbstractPO(String name, 
                      ModelClass modelClass) {
        this.name       = name;
        this.modelClass = modelClass;
    }

    //-------------------------------------------------------------------------
    //helper methods for subclasses
    //-------------------------------------------------------------------------

    protected ProgramVariable buildSelfVarAsProgVar() {
        String className = modelClass.getFullClassName();
        KeYJavaType classType = javaInfo.getTypeByClassName(className);

        ProgramElementName classPEN = new ProgramElementName("self");
        
        return new LocationVariable(classPEN, classType);     
    }


    protected LogicVariable buildSelfVarAsLogicVar() {
        String className = modelClass.getFullClassName();
        KeYJavaType classType = javaInfo.getTypeByClassName(className);

        ProgramElementName classPEN = new ProgramElementName("self");
        return new LogicVariable(classPEN, classType.getSort());       
    }


    protected ListOfProgramVariable buildParamVars(ModelMethod modelMethod) {
        int numPars = modelMethod.getNumParameters();
        ListOfProgramVariable result = SLListOfProgramVariable.EMPTY_LIST;

        for(int i = 0; i < numPars; i++) {
            KeYJavaType parType
                    = javaInfo.getTypeByClassName(modelMethod.getParameterTypeAt(i));
            assert parType != null;
            ProgramElementName parPEN
                    = new ProgramElementName(modelMethod.getParameterNameAt(i));
            result = result.append(new LocationVariable(parPEN, parType));
        }

        return result;
    }


    protected ProgramVariable buildResultVar(ModelMethod modelMethod) {
        ProgramVariable result = null;

        if(!modelMethod.isVoid()) {
            KeYJavaType resultType
                    = javaInfo.getTypeByClassName(modelMethod.getResultType());
            assert resultType != null;
            ProgramElementName resultPEN = new ProgramElementName("result");
            result = new LocationVariable(resultPEN, resultType);
        }

        return result;
    }


    protected ProgramVariable buildExcVar() {
        KeYJavaType excType 
        	= javaInfo.getTypeByClassName("java.lang.Throwable");
        ProgramElementName excPEN = new ProgramElementName("exc");
        return new LocationVariable(excPEN, excType);      
    }
    

    /**
     * Translates a precondition out of an operation contract.
     * @throws SLTranslationError 
     */
    protected Term translatePre(OperationContract contract,
                                ParsableVariable selfVar,
                                ListOfParsableVariable paramVars) throws SLTranslationError {
        FormulaWithAxioms fwa = contract.getPre(selfVar, paramVars, services);
        axioms.putAll(fwa.getAxioms());
        return fwa.getFormula();
    }


    /**
     * Translates a postcondition out of an operation contract.
     * @throws SLTranslationError 
     */
    protected Term translatePost(OperationContract contract,
                                 ParsableVariable selfVar,
                                 ListOfParsableVariable paramVars,
                                 ParsableVariable resultVar,
                                 ParsableVariable excVar) throws SLTranslationError {
        FormulaWithAxioms fwa = contract.getPost(selfVar, 
        					 paramVars, 
        					 resultVar, 
        					 excVar, 
        					 services);
        axioms.putAll(fwa.getAxioms());
        return fwa.getFormula();
    }


    /**
     * Translates a modifies clause out of an operation contract.
     */
    protected Term translateModifies(OperationContract contract,
                                     Term targetTerm,
                                     ParsableVariable selfVar,
                                     ListOfParsableVariable paramVars) throws SLTranslationError{
        final SetOfLocationDescriptor locations = 
            contract.getModifies(selfVar, paramVars, services);

        final UpdateFactory uf = new UpdateFactory(services, new UpdateSimplifier());
        final AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);
        return auf.createAnonymisingUpdateTerm(locations,
                                               targetTerm,
                                               services);       
    }
    
    
    /**
     * Translates a class invariant.
     * @throws SLTranslationError 
     */
    protected Term translateInv(ClassInvariant inv) throws SLTranslationError {
        final FormulaWithAxioms fwa = inv.getInv(services);
        axioms.putAll(fwa.getAxioms());
        return fwa.getFormula();
    }
    
    
    /**
     * Translates a list of class invariants.
     * @throws SLTranslationError 
     */
    protected Term translateInvs(ListOfClassInvariant invs) throws SLTranslationError {
	Term result = tb.tt();
	
	IteratorOfClassInvariant it = invs.iterator();
	while(it.hasNext()) {
	    result = tb.and(result, translateInv(it.next()));
	}
	
	return result;
    }
    
    
    /**
     * Translates a class invariant as an open formula.
     * @throws SLTranslationError 
     */
    protected Term translateInvOpen(ClassInvariant inv, 
	    			    ParsableVariable selfVar) throws SLTranslationError {
	FormulaWithAxioms fwa = inv.getOpenInv(selfVar, services);
	axioms.putAll(fwa.getAxioms());
	return fwa.getFormula();
    }
    
    
    protected Term translateInvsOpen(ListOfClassInvariant invs, 
	    			     ParsableVariable selfVar) throws SLTranslationError {
	Term result = tb.tt();
	
	IteratorOfClassInvariant it = invs.iterator();
	while(it.hasNext()) {
	    result = tb.and(result, translateInvOpen(it.next(), selfVar));
	}
	
	return result;
    }
    
    
    protected ListOfParsableVariable toPV(ListOfProgramVariable vars) {
	ListOfParsableVariable result = SLListOfParsableVariable.EMPTY_LIST;
	final IteratorOfProgramVariable it = vars.iterator();
	while(it.hasNext()) {
	    result = result.append(it.next());
	}
	return result;
    }



    /**
     * Replaces operators in a term by other operators with the same signature.
     */
    protected Term replaceOps(Map /*Operator -> Operator*/ map, Term term) {      
        return new OpReplacer(map).replace(term);
    }


    /**
     * Creates atPre-functions for all relevant operators in the passed term.
     */
    public static void createAtPreFunctionsForTerm(
	    		Term term,
                        /*inout*/Map /*Operator -> Function*/atPreFunctions) {
        int arity = term.arity();
        Sort[] subSorts = new Sort[arity];
        for(int i = 0; i < arity; i++) {
            Term subTerm = term.sub(i);
            createAtPreFunctionsForTerm(subTerm, atPreFunctions);
            subSorts[i] = subTerm.sort();
        }

        if(term.op() instanceof AccessOp
           || term.op() instanceof ProgramVariable
           || term.op() instanceof ProgramMethod) {
            Function atPreFunc = (Function)(atPreFunctions.get(term.op()));
            if(atPreFunc == null) {
                String atPreName = term.op().name().toString() + "@pre";
                if(atPreName.startsWith(".")) {
                    atPreName = atPreName.substring(1);
                }
                atPreFunc = new RigidFunction(new Name(atPreName),
                                              term.sort(),
                                              subSorts);
                atPreFunctions.put(term.op(), atPreFunc);
            }
        }
    }
    
    /**
     * Helper for buildAtPreDefinitions().
     */
    private static Term[] getTerms(ArrayOfQuantifiableVariable vars) {
        int numVars = vars.size();
        Term[] result = new Term[numVars];

        for(int i = 0; i < numVars; i++) {
            LogicVariable var
                    = (LogicVariable)(vars.getQuantifiableVariable(i));
            result[i] = tb.var(var);
        }

        return result;
    }


    /**
     * Creates the necessary definitions for the passed @pre-functions.
     */
    public static Term buildAtPreDefinitions(
	    		/*in*/ Map /*Operator -> Function */atPreFunctions) {
        Term result = tb.tt();

        Iterator it = atPreFunctions.entrySet().iterator();
        while(it.hasNext()) {
            Map.Entry entry = (Map.Entry)(it.next());
            Operator f1 = (Operator)(entry.getKey());
            Function f2 = (Function)(entry.getValue());

            int arity = f1.arity();
            assert arity == f2.arity();
            LogicVariable[] args = new LogicVariable[arity];
            for(int i = 0; i < arity; i++) {
                args[i] = new LogicVariable(new Name("x" + i), f2.argSort(i));
            }

            Term[] argTerms = getTerms(new ArrayOfQuantifiableVariable(args));

            Term f1Term = tf.createTerm(f1,
                                        argTerms,
                                        (ArrayOfQuantifiableVariable)null,
                                        null);
            Term f2Term = tb.func(f2, argTerms);
            Term equalsTerm = tf.createJunctorTerm(Op.EQUALS, f1Term, f2Term);
            Term quantifTerm;
            if(arity > 0) {
                quantifTerm = tb.all(args, equalsTerm);
            } else {
                quantifTerm = equalsTerm;
            }
            result = tb.and(result, quantifTerm);
        }

        return result;
    }


    protected void registerInNamespaces(ProgramVariable pv) {
        if(pv != null) {
            initConfig.progVarNS().add(pv);
        }
    }


    protected void registerInNamespaces(ListOfProgramVariable pvs) {
        final IteratorOfProgramVariable it = pvs.iterator();
        while(it.hasNext()) {
            initConfig.progVarNS().add(it.next());
        }
    }


    protected void registerInNamespaces(/*in*/ Map atPreFunctions) {
        final Iterator it = atPreFunctions.values().iterator();  
        while(it.hasNext()) {            
            initConfig.funcNS().add((Function) it.next()); 
        }
    }
    


    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------
    
    public String name() {
        return name;
    }
    

    public boolean askUserForEnvironment() {
        return false;
    }
    
    
    public void setInitConfig(InitConfig initConfig) {
        this.initConfig = initConfig;
        this.services   = initConfig.getServices();
        this.javaInfo   = initConfig.getServices().getJavaInfo();
    }
    
    
    public void readActivatedChoices() throws ProofInputException {
	initConfig.setActivatedChoices(SetAsListOfChoice.EMPTY_SET);
    }
    
    
    /**
     * Computes the method specifications and stores the results in the
     * SpecificationRepository which belongs to the ProofEnvironment of InitCfg.
     */
    public void readSpecs(){
      // specifications from model
        Vector reprMethods = null;
        Iterator reprMethodsIter = null;
        UMLModelClass reprClass = null;
        Set allClasses = modelClass.getAllClasses();
        Iterator allClassesIter = allClasses.iterator();
        while (allClassesIter.hasNext()){
            reprClass = (UMLModelClass) allClassesIter.next();
            reprMethods = reprClass.getOps();
            reprMethodsIter = reprMethods.iterator();
            while(reprMethodsIter.hasNext()){
                ListOfOperationContract l 
                = ((ModelMethod)reprMethodsIter.next()).getMyOperationContracts();
                IteratorOfOperationContract it = l.iterator();
                /*TODO
                while (it.hasNext()) {
                    initConfig.getProofEnv().addMethodContract(it.next());
                }*/
            }
        }
    }

    
    
    /**
     * Creates declarations necessary to save/load proof in textual form
     * (helper for createProof()).
     */
    private String createProofHeader(String javaPath) {
        if(header != null) {
            return header;
        }

        String s;
        s = "\\javaSource \""+javaPath+"\";\n\n";

        IteratorOfNamed it;

        /* program sorts need not be declared and
         * there are no user-defined sorts with this kind of PO (yes?)
                s += "sorts {\n"; // create declaration header for the proof
                it = initConfig.sortNS().getProtocolled();
                while (it.hasNext()) {
                String n=it.next().toString();
                int i;
                if ((i=n.indexOf("."))<0 ||
                initConfig.sortNS().lookup(new Name(n.substring(0,i)))==null) {
                //the line above is for inner classes.
                //KeY does not want to handle them anyway...
                s = s+"object "+n+";\n";
                }
            }
                s+="}
        */
        s += "\n\n\\programVariables {\n";
        it = initConfig.progVarNS().allElements().iterator();
        while(it.hasNext())
           s = s+((ProgramVariable)(it.next())).proofToString();
        
        s += "}\n\n\\functions {\n";
        it = initConfig.funcNS().allElements().iterator();
        while(it.hasNext()) {
            Function f = (Function)it.next();
            // only declare @pre-functions, others will be generated automat.
            if(f.name().toString().indexOf("@pre")!=-1) {
                s += f.proofToString();
            }
        }

        s += "}\n\n";

        header = s;
        return s;
    }


    /**
     * Creates a Proof (helper for getPO()).
     */
    private Proof createProof(String name, Term poTerm) {
        if(header == null) {
            header = createProofHeader(modelClass.getRootDirectory());
        }
        return new Proof(name,
                         poTerm,
                         header,
                         initConfig.createTacletIndex(),
                         initConfig.createBuiltInRuleIndex(),
                         initConfig.getServices());
    }


    /**
     * Returns those axioms from the SLDL-Translation which are required for
     * the passed term (helper for getPO()).
     */
    private Term getRequiredAxioms(Term t) {
        Term result = tb.tt();

        Set axiomSet = getRequiredAxiomsAsSet(t);
        
        Iterator it = axiomSet.iterator();
        while(it.hasNext()) {
            result = tb.and(result,(Term)it.next());
        }
/*        
        if(axioms.containsKey(t.op())) {            
            result = tb.and(result, (Term)axioms.get(t.op()));
        }
    
        for(int i = 0; i < t.arity(); i++) {
            result = tb.and(result, getRequiredAxioms(t.sub(i)));
        }
*/    
        return result;
    }
      

    /**
     * Returns those axioms from the SLDL-Translation which are required for
     * the passed term (helper for getRequiredAxioms(Term t)).
     */
    private Set getRequiredAxiomsAsSet(Term t) {
        Set result = new HashSet();
        
        if (axioms.containsKey(t.op())) {
            result.add(axioms.get(t.op()));
        }
        
        for(int i = 0; i < t.arity(); i++) {
            result.addAll(getRequiredAxiomsAsSet(t.sub(i)));
        }
        
        return result;
    }
    
    
    public ProofAggregate getPO() {
        if(proofAggregate != null) {
            return proofAggregate;
        }
        
        if(poTerms == null) {
            throw new IllegalStateException("No proof obligation terms.");
        }
        
        Proof[] proofs = new Proof[poTerms.length];
        for(int i = 0; i < proofs.length; i++) {
            proofs[i] = createProof(poNames != null ? poNames[i] : name, 
                                    tb.imp(getRequiredAxioms(poTerms[i]), 
                                           poTerms[i]));
            
            if(poTaclets != null) {
                proofs[i].getGoal(proofs[i].root()).indexOfTaclets()
                                                   .addTaclets(poTaclets[i]);
            }
        }
        
        return proofAggregate = ProofAggregate.createProofAggregate(proofs, name);
    }
}
