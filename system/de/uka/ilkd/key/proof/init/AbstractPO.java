// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
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
import de.uka.ilkd.key.speclang.Contract;
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

    private final List<ProgramVariable> introducedProgVars 
    	= new LinkedList<ProgramVariable>();
    private final List<Function> introducedFuncs
    	= new LinkedList<Function>();
    private final List<Function> introducedPreds
    	= new LinkedList<Function>();
    private ImmutableSet<NoPosTacletApp> taclets;    
    private String header;
    private ProofAggregate proofAggregate;    
    
    protected Term[] poTerms;
    protected String[] poNames;    

    
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
    
        
    protected void collectClassAxioms(KeYJavaType selfKJT) {
	taclets = DefaultImmutableSet.nil();
	final ImmutableSet<ClassAxiom> axioms 
		= specRepos.getClassAxioms(selfKJT);
	
	for(ClassAxiom axiom : axioms) {
	    final ImmutableSet<Pair<Sort, ObserverFunction>> scc 
	    	= getSCC(axiom, axioms);
	    for(Taclet axiomTaclet : axiom.getTaclets(scc, services)) {
		assert axiomTaclet != null 
		       : "class axiom returned null taclet: " + axiom.getName();
		taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(
				   				axiomTaclet));
		initConfig.getProofEnv()
			  .registerRule(axiomTaclet, 
				  	AxiomJustification.INSTANCE);
	    }	    
	}
    }    
    
    
    
    protected final void register(ProgramVariable pv) {
	if(pv != null) {
	    introducedProgVars.add(pv);
	}
    }
    
    
    protected final void register(ImmutableList<ProgramVariable> pvs) {
	for(ProgramVariable pv : pvs) {
	    register(pv);
	}
    }
    
    
    protected final void register(Function f) {
	if(f != null) {
	    assert f.sort() != Sort.UPDATE;
	    if(f.sort() == Sort.FORMULA) {
		introducedPreds.add(f);
	    } else {
		introducedFuncs.add(f);
	    }
	}
    }
    

    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    @Override
    public final String name() {
        return name;
    }

    
    /**
     * Creates declarations necessary to save/load proof in textual form
     * (helper for createProof()).
     */
    private void createProofHeader(String javaPath,
	    			   String classPath,
	    			   String bootClassPath) {
        if(header != null) {
            return;
        }
        final StringBuffer sb = new StringBuffer();
        
        //bootclasspath
        if(bootClassPath != null && !bootClassPath.equals("")) {
            sb.append("\\bootclasspath \"")
              .append(bootClassPath)
              .append("\";\n\n");
        }
        
        //classpath
        if(classPath != null && !classPath.equals("")) {
            sb.append("\\classpath \"")
              .append(classPath)
              .append("\";\n\n");
        }        

        //javaSource
        sb.append("\\javaSource \"")
          .append(javaPath)
          .append("\";\n\n");

        //contracts
        ImmutableSet<Contract> contractsToSave = specRepos.getAllContracts();
        for(Contract c : contractsToSave) {
            if(!c.toBeSaved()) {
        	contractsToSave = contractsToSave.remove(c);
            }
        }
        if(!contractsToSave.isEmpty()) {
            sb.append("\\contracts {\n");
            for(Contract c : contractsToSave) {
        	sb.append(c.proofToString(services));
            }
            sb.append("}\n\n");
        }

        header = sb.toString();
    }


    /**
     * Creates a Proof (helper for getPO()).
     */
    private Proof createProof(String proofName, Term poTerm) {
	final JavaModel javaModel = initConfig.getProofEnv().getJavaModel();
	createProofHeader(javaModel.getModelDir(), 
			  javaModel.getClassPath(),
			  javaModel.getBootClassPath());
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
            if(taclets != null) {
                proofs[i].getGoal(proofs[i].root()).indexOfTaclets()
                                                   .addTaclets(taclets);
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
