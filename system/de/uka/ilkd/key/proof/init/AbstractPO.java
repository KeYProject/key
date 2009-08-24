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
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;



/**
 * An abstract proof obligation implementing common functionality.
 */
public abstract class AbstractPO implements ProofOblInput {

    protected static final TermFactory TF = TermFactory.DEFAULT;
    protected static final TermBuilder TB = TermBuilder.DF;

    protected final InitConfig initConfig;
    protected final Services services;
    protected final JavaInfo javaInfo;
    protected final HeapLDT heapLDT;
    protected final SpecificationRepository specRepos;
    protected final String name;
    protected final KeYJavaType selfKJT;

    private String header;
    private ProofAggregate proofAggregate;
    
    protected Term[] poTerms;
    protected String[] poNames;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public AbstractPO(InitConfig initConfig, String name, KeYJavaType selfKJT) {
	this.initConfig = initConfig;
        this.services   = initConfig.getServices();
        this.javaInfo   = initConfig.getServices().getJavaInfo();
        this.heapLDT    = initConfig.getServices().getTypeConverter().getHeapLDT();
        this.specRepos  = initConfig.getServices().getSpecificationRepository();
        this.name       = name;
        this.selfKJT    = selfKJT;
    }

    
    
    //-------------------------------------------------------------------------
    //helper methods for subclasses
    //-------------------------------------------------------------------------

    protected final ProgramVariable buildSelfVarAsProgVar() {
        return new LocationVariable(new ProgramElementName("self"), selfKJT);
    }
    

    protected final ImmutableList<ProgramVariable> buildParamVars(
	    				ProgramMethod programMethod) {
        int numPars = programMethod.getParameterDeclarationCount();
        ImmutableList<ProgramVariable> result 
        	= ImmutableSLList.<ProgramVariable>nil();

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


    protected final ProgramVariable buildResultVar(ProgramMethod programMethod){
        final KeYJavaType resultKJT = programMethod.getKeYJavaType();
        if(resultKJT != null) {
            final ProgramElementName resultPEN 
            	= new ProgramElementName("result");
            return new LocationVariable(resultPEN, resultKJT);
        }
        return null;
    }


    protected final ProgramVariable buildExcVar() {
        final KeYJavaType excType
        	= javaInfo.getTypeByClassName("java.lang.Throwable");
        return new LocationVariable(new ProgramElementName("exc"), excType);      
    }
    
    /**
     * Replaces operators in a term by other operators with the same signature.
     */
    protected final Term replaceOps(Map<? extends Operator, ? extends Operator> map, Term term) {      
        return new OpReplacer(map).replace(term);
    }


    protected final void registerInNamespaces(ProgramVariable pv) {
        if(pv != null) {
            initConfig.progVarNS().add(pv);
        }
    }

    protected final void registerInNamespaces(Function f) {
        if(f != null) {
            services.getNameRecorder().addProposal(f.name());
            initConfig.funcNS().add(f);
        }
    }


    protected final void registerInNamespaces(ImmutableList<ProgramVariable> pvs) {
        final Iterator<ProgramVariable> it = pvs.iterator();
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
	initConfig.setActivatedChoices(DefaultImmutableSet.<Choice>nil());
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

        Iterator<Named> it;

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
        }
        
        return proofAggregate = ProofAggregate.createProofAggregate(proofs, name);
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }
}
