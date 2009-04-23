// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.AnonymisingUpdateFactory;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SetAsListOfChoice;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.SetOfTaclet;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.speclang.*;



/**
 * An abstract proof obligation implementing common functionality.
 */
public abstract class AbstractPO implements ProofOblInput {

    protected static final TermFactory TF = TermFactory.DEFAULT;
    protected static final CreatedAttributeTermFactory CATF
                                   = CreatedAttributeTermFactory.INSTANCE;
    protected static final TermBuilder TB = TermBuilder.DF;
    protected static final AtPreFactory APF = AtPreFactory.INSTANCE;

    protected final InitConfig initConfig;
    protected final Services services;
    protected final JavaInfo javaInfo;
    protected final SpecificationRepository specRepos;
    protected final UpdateFactory uf;
    protected final String name;
    protected final KeYJavaType selfKJT;

    private final Map<Operator, Term> axioms = new LinkedHashMap<Operator, Term>();
    private String header;
    private ProofAggregate proofAggregate;
    
    protected Term[] poTerms;
    protected String[] poNames;
    protected SetOfTaclet[] poTaclets;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public AbstractPO(InitConfig initConfig, String name, KeYJavaType selfKJT) {
	this.initConfig = initConfig;
        this.services   = initConfig.getServices();
        this.javaInfo   = initConfig.getServices().getJavaInfo();
        this.specRepos  = initConfig.getServices().getSpecificationRepository();
        this.uf         = new UpdateFactory(services, new UpdateSimplifier());
        this.name       = name;
        this.selfKJT    = selfKJT;
    }

    //-------------------------------------------------------------------------
    //helper methods for subclasses
    //-------------------------------------------------------------------------

    protected ProgramVariable buildSelfVarAsProgVar() {
        return new LocationVariable(new ProgramElementName("self"), selfKJT);
    }

    protected LogicVariable buildSelfVarAsLogicVar() {
        return new LogicVariable(new ProgramElementName("self"), selfKJT.getSort());
    }

    protected ListOfProgramVariable buildParamVars(ProgramMethod programMethod) {
        int numPars = programMethod.getParameterDeclarationCount();
        ListOfProgramVariable result = SLListOfProgramVariable.EMPTY_LIST;

        for(int i = 0; i < numPars; i++) {
            KeYJavaType parType = programMethod.getParameterType(i);
            assert parType != null;
            String parName = programMethod.getParameterDeclarationAt(i)
            				  .getVariableSpecification()
            				  .getName();
            ProgramElementName parPEN = new ProgramElementName(parName);
            result = result.append(new LocationVariable(parPEN, parType));
        }

        return result;
    }


    protected ProgramVariable buildResultVar(ProgramMethod programMethod) {
        final KeYJavaType resultKJT = programMethod.getKeYJavaType();
        if(resultKJT != null) {
            final ProgramElementName resultPEN = new ProgramElementName("result");
            return new LocationVariable(resultPEN, resultKJT);
        }
        return null;
    }


    protected ProgramVariable buildExcVar() {
        final KeYJavaType excType
        	= javaInfo.getTypeByClassName("java.lang.Throwable");
        return new LocationVariable(new ProgramElementName("exc"), excType);      
    }
    

    /**
     * Translates a precondition out of an operation contract. 
     */
    protected Term translatePre(OperationContract contract,
                                ParsableVariable selfVar,
                                ListOfParsableVariable paramVars) 
    		throws ProofInputException {
        FormulaWithAxioms fwa = contract.getPre(selfVar, paramVars, services);
        axioms.putAll(fwa.getAxioms());
        return fwa.getFormula();
    }


    /**
     * Translates a postcondition out of an operation contract. 
     */
    protected Term translatePost(OperationContract contract,
                                 ParsableVariable selfVar,
                                 ListOfParsableVariable paramVars,
                                 ParsableVariable resultVar,
                                 ParsableVariable excVar,
                                 /*inout*/ Map<Operator, Function/*(atPre)*/> atPreFunctions) 
    		throws ProofInputException {
        FormulaWithAxioms fwa = contract.getPost(selfVar, 
        					 paramVars, 
        					 resultVar, 
        					 excVar, 
                                                 atPreFunctions,
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
                                     ListOfParsableVariable paramVars) 
    		throws ProofInputException {
        SetOfLocationDescriptor locations = contract.getModifies(selfVar,
                                                                 paramVars,
                                                                 services);

        UpdateFactory uf = new UpdateFactory(services, new UpdateSimplifier());
        AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);
        return auf.createAnonymisingUpdateTerm(locations,
                targetTerm,
                services);
    }
    
    
    /**
     * Translates a class invariant. 
     */
    protected Term translateInv(ClassInvariant inv) 
    		throws ProofInputException {
        final FormulaWithAxioms fwa = inv.getClosedInv(services);
        axioms.putAll(fwa.getAxioms());
        return fwa.getFormula();
    }
    
    
    /**
     * Translates a list of class invariants. 
     */
    protected Term translateInvs(SetOfClassInvariant invs) 
    		throws ProofInputException {
	Term result = TB.tt();
	for (final ClassInvariant inv : invs) {
	    result = TB.and(result, translateInv(inv));
	}
	return result;
    }
    
    
    /**
     * Translates a class invariant as an open formula. 
     */
    protected Term translateInvOpen(ClassInvariant inv, 
	    			    ParsableVariable selfVar) 
    		throws ProofInputException {
        FormulaWithAxioms fwa = inv.getOpenInv(selfVar, services);
        axioms.putAll(fwa.getAxioms());
        return fwa.getFormula();
    }
    
    
    protected Term translateInvsOpen(SetOfClassInvariant invs, 
	    			     ParsableVariable selfVar) 
    		throws ProofInputException {
	Term result = TB.tt();
	for (final ClassInvariant inv : invs) {
	    result = TB.and(result, translateInvOpen(inv, selfVar));
	}
	return result;
    }
    
    
    protected ListOfParsableVariable toPV(ListOfProgramVariable vars) {
	ListOfParsableVariable result = SLListOfParsableVariable.EMPTY_LIST;
	for (final ProgramVariable pv : vars) {
	    result = result.append(pv);
	}
	return result;
    }

    
    /**
     * Replaces operators in a term by other operators with the same signature.
     */
    protected Term replaceOps(Map<? extends Operator, ? extends Operator> map, Term term) {      
        return new OpReplacer(map).replace(term);
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


    protected void registerInNamespaces(/*in*/ Map<Operator, Function> atPreFunctions) {
        for (final Function atPreF : atPreFunctions.values()) {
            initConfig.funcNS().add(atPreF); 
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
    
        
    public void readActivatedChoices() throws ProofInputException {
	initConfig.setActivatedChoices(SetAsListOfChoice.EMPTY_SET);
    }

    
    /**
     * Creates declarations necessary to save/load proof in textual form
     * (helper for createProof()).
     */
    private void createProofHeader(String javaPath) {
        if(header != null) {
            return;
        }
                
        if(initConfig.getOriginalKeYFileName() == null) {
            header = "\\javaSource \""+javaPath+"\";\n\n";
        } else {
            header = "\\include \"./" + initConfig.getOriginalKeYFileName() + "\";";
        }

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
        header += "\n\n\\programVariables {\n";
        it = initConfig.progVarNS().allElements().iterator();
        while(it.hasNext())
        header += ((ProgramVariable)(it.next())).proofToString();
        
        header += "}\n\n\\functions {\n";
        it = initConfig.funcNS().allElements().iterator();
        while(it.hasNext()) {
            Function f = (Function)it.next();
            // only declare @pre-functions or anonymising functions, others will be generated automat. (hack)
            if(f.name().toString().indexOf("AtPre")!=-1 || services.getNameRecorder().
                    getProposals().contains(f.name())) {
                header += f.proofToString();
            }
        }

        header += "}\n\n";
    }


    /**
     * Creates a Proof (helper for getPO()).
     */
    private Proof createProof(String name, Term poTerm) {
         createProofHeader(initConfig.getProofEnv()
   	    		             .getJavaModel()
        	    	             .getModelDir());
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
        Term result = TB.tt();

        final Set<Term> axiomSet = getRequiredAxiomsAsSet(t);
        
        for (final Term axiom : axiomSet) {
            result = TB.and(result, axiom);
        }
/*        
        if(axioms.containsKey(t.op())) {            
            result = TB.and(result, (Term)axioms.get(t.op()));
        }
    
        for(int i = 0; i < t.arity(); i++) {
            result = TB.and(result, getRequiredAxioms(t.sub(i)));
        }
*/    
        return result;
    }
      

    /**
     * Returns those axioms from the SLDL-Translation which are required for
     * the passed term (helper for getRequiredAxioms(Term t)).
     */
    private Set<Term> getRequiredAxiomsAsSet(Term t) {
        Set<Term> result = new LinkedHashSet<Term>();
        
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
            Term axioms = getRequiredAxioms(poTerms[i]);
            proofs[i] = createProof(poNames != null ? poNames[i] : name,
                                    poTerms[i].op() == Op.IMP
                                    ? TB.imp(TB.and(axioms, poTerms[i].sub(0)),
                                             poTerms[i].sub(1))
                                    : TB.imp(axioms, poTerms[i]));
            
            if(poTaclets != null) {
                proofs[i].getGoal(proofs[i].root()).indexOfTaclets()
                                                   .addTaclets(poTaclets[i]);
            }
        }
        
        return proofAggregate = ProofAggregate.createProofAggregate(proofs, name);
    }
    
    
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }
}
