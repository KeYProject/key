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

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.util.Pair;



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

    private String header;
    private ProofAggregate proofAggregate;
    
    protected Term[] poTerms;
    protected String[] poNames;
    protected ImmutableSet<NoPosTacletApp>[] poTaclets;    

    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public AbstractPO(InitConfig initConfig, String name) {
	this.initConfig = initConfig;
        this.services   = initConfig.getServices();
        this.javaInfo   = initConfig.getServices().getJavaInfo();
        this.heapLDT    = initConfig.getServices().getTypeConverter().getHeapLDT();
        this.specRepos  = initConfig.getServices().getSpecificationRepository();
        this.name       = name;
    }
    
    
    
    //-------------------------------------------------------------------------
    //methods for use in subclasses
    //-------------------------------------------------------------------------
    
    private ImmutableSet<ClassAxiom> getAxiomsForObserver(
	    				Pair<Sort, ObserverFunction> usedObs,
	    				ImmutableSet<ClassAxiom> axioms) {
	for(ClassAxiom axiom : axioms) {
	    if(!(axiom.getTarget().equals(usedObs.second) 
		 && usedObs.first.extendsTrans(axiom.getKJT().getSort()))) {
		axioms = axioms.remove(axiom);
	    }
	}
	return axioms;
    }
    
    
    private boolean reach(Pair<Sort, ObserverFunction> from, 
	    		  Pair<Sort, ObserverFunction> to, 
	    	 	  ImmutableSet<ClassAxiom> axioms) {
	ImmutableSet<Pair<Sort, ObserverFunction>> reached
		= DefaultImmutableSet.nil();	
	ImmutableSet<Pair<Sort, ObserverFunction>> newlyReached
		= DefaultImmutableSet.<Pair<Sort, ObserverFunction>>nil()
		                     .add(from);
	
	while(!newlyReached.isEmpty()) {
	    for(Pair<Sort, ObserverFunction> node : newlyReached) {
		newlyReached = newlyReached.remove(node);
		reached = reached.add(node);
		final ImmutableSet<ClassAxiom> nodeAxioms 
			= getAxiomsForObserver(node, axioms);
		for(ClassAxiom nodeAxiom : nodeAxioms) {
		    final ImmutableSet<Pair<Sort,ObserverFunction>> nextNodes
		    	= nodeAxiom.getUsedObservers(services);
		    for(Pair<Sort,ObserverFunction> nextNode : nextNodes) {
			if(nextNode.equals(to)) {
			    return true;
			} else if(!reached.contains(nextNode)) {
			    newlyReached = newlyReached.add(nextNode);
			}
		    }
		}
	    }
	}
	
	return false;
    }
    
    
    private ImmutableSet<Pair<Sort, ObserverFunction>> 
    				getSCC(ClassAxiom startAxiom,
    				       ImmutableSet<ClassAxiom> axioms) {
	//TODO: make more efficient	
	final Pair<Sort, ObserverFunction> start 
	    = new Pair<Sort, ObserverFunction>(startAxiom.getKJT().getSort(), 
					       startAxiom.getTarget());
	ImmutableSet<Pair<Sort, ObserverFunction>> result 
		= DefaultImmutableSet.nil();
	for(ClassAxiom nodeAxiom : axioms) {
	    final Pair<Sort, ObserverFunction> node 
	    	= new Pair<Sort, ObserverFunction>(nodeAxiom.getKJT().getSort(), 
	    					   nodeAxiom.getTarget());
	    if(reach(start, node, axioms) && reach(node, start, axioms)) {
		result = result.add(node);
	    }
	}
	return result;
    }
    
        
    protected final ImmutableSet<NoPosTacletApp> collectClassAxioms(
	    						KeYJavaType selfKJT) {
	ImmutableSet<NoPosTacletApp> result = DefaultImmutableSet.nil();
	final ImmutableSet<ClassAxiom> axioms 
		= specRepos.getClassAxioms(selfKJT);
	
	for(ClassAxiom axiom : axioms) {
	    final ImmutableSet<Pair<Sort, ObserverFunction>> scc 
	    	= getSCC(axiom, axioms);
//	    for(Pair<Sort, ObserverFunction> sccAx : scc) {
//		System.out.println("in scc of " + axiom.getName() + ": " + sccAx);
//	    }
	    for(Taclet axiomTaclet : axiom.getTaclets(scc, services)) {
		assert axiomTaclet != null 
		       : "class axiom returned null taclet: " + axiom.getName();
		result = result.add(NoPosTacletApp.createNoPosTacletApp(
				   				axiomTaclet));
		initConfig.getProofEnv()
			  .registerRule(axiomTaclet, 
				  	AxiomJustification.INSTANCE);
	    }	    
	}

	return result;
    }    

    
    //-------------------------------------------------------------------------
    //public interface
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
    private Proof createProof(String proofName, Term poTerm) {
         createProofHeader(initConfig.getProofEnv()
   	    		             .getJavaModel()
        	    	             .getModelDir());
        return new Proof(proofName,
                         poTerm,
                         header,
                         initConfig.createTacletIndex(),
                         initConfig.createBuiltInRuleIndex(),
                         initConfig.getServices(),
                         initConfig.getSettings() != null 
                          ? initConfig.getSettings() 
                          : new ProofSettings(ProofSettings.DEFAULT_SETTINGS));
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
        
        proofAggregate = ProofAggregate.createProofAggregate(proofs, name);
        return proofAggregate;
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }
}
