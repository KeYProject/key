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

import java.util.*;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SetAsListOfChoice;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.SetOfTaclet;
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
                                ProgramVariable selfVar,
                                ListOfProgramVariable paramVars) 
    		throws ProofInputException {
        FormulaWithAxioms fwa = contract.getPre(selfVar, paramVars, services);
        axioms.putAll(fwa.getAxioms());
        return fwa.getFormula();
    }


    /**
     * Translates a postcondition out of an operation contract. 
     */
    protected Term translatePost(OperationContract contract,
                                 ProgramVariable selfVar,
                                 ListOfProgramVariable paramVars,
                                 ProgramVariable resultVar,
                                 ProgramVariable excVar,
                                 Term heapAtPre) 
    		throws ProofInputException {
        FormulaWithAxioms fwa = contract.getPost(selfVar, 
        					 paramVars, 
        					 resultVar, 
        					 excVar, 
                                                 heapAtPre,
        					 services);
        axioms.putAll(fwa.getAxioms());
        return fwa.getFormula();
    }


    /**
     * Translates a modifies clause out of an operation contract.
     */
    protected Term translateModifies(OperationContract contract,
                                     Term targetTerm,
                                     ProgramVariable selfVar,
                                     ListOfProgramVariable paramVars) 
    		throws ProofInputException {
	assert false : "not implemented";
    	return null;
//        SetOfLocationDescriptor locations = contract.getModifies(selfVar,
//                                                                 paramVars,
//                                                                 services);
//
//        UpdateFactory uf = new UpdateFactory(services, new OldUpdateSimplifier());
//        AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);
//        return auf.createAnonymisingUpdateTerm(locations,
//                targetTerm,
//                services);
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
	    			    ProgramVariable selfVar) 
    		throws ProofInputException {
        FormulaWithAxioms fwa = inv.getOpenInv(selfVar, services);
        axioms.putAll(fwa.getAxioms());
        return fwa.getFormula();
    }
    
    
    protected Term translateInvsOpen(SetOfClassInvariant invs, 
	    			     ProgramVariable selfVar) 
    		throws ProofInputException {
	Term result = TB.tt();
	for (final ClassInvariant inv : invs) {
	    result = TB.and(result, translateInvOpen(inv, selfVar));
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

    protected void registerInNamespaces(Function f) {
        if(f != null) {
            services.getNameRecorder().addProposal(f.name());
            initConfig.funcNS().add(f);
        }
    }


    protected void registerInNamespaces(ListOfProgramVariable pvs) {
        final IteratorOfProgramVariable it = pvs.iterator();
        while(it.hasNext()) {
            initConfig.progVarNS().add(it.next());
        }
    }


    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------
    
    @Override
    public final String name() {
        return name;
    }
    
        
    @Override
    public final void readActivatedChoices() throws ProofInputException {
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
            if(f.sort() != Sort.FORMULA && (f.name().toString().indexOf("AtPre")!=-1 || services.getNameRecorder().
                    getProposals().contains(f.name()))) {
                header += f.proofToString();
            }
        }
        header += "}\n\n\\predicates {\n";

        it = initConfig.funcNS().allElements().iterator();
        while(it.hasNext()) {
            Function f = (Function)it.next();            
            if(f.sort() == Sort.FORMULA && services.getNameRecorder().getProposals().contains(f.name())) {
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

    
    @Override
    public final ProofAggregate getPO() {
        if(proofAggregate != null) {
            return proofAggregate;
        }
        
        if(poTerms == null) {
            throw new IllegalStateException("No proof obligation terms.");
        }
        
        Proof[] proofs = new Proof[poTerms.length];
        for(int i = 0; i < proofs.length; i++) {
            proofs[i] = createProof(poNames != null ? poNames[i] : name,
                                    poTerms[i]);
            
            if(poTaclets != null) {
                proofs[i].getGoal(proofs[i].root()).indexOfTaclets()
                                                   .addTaclets(poTaclets[i]);
            }
        }
        
        return proofAggregate = ProofAggregate.createProofAggregate(proofs, name);
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }
}
