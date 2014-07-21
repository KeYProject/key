// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.dl.translation;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.ClassInvariantImpl;
import de.uka.ilkd.key.speclang.ContractFactory;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;


/**
 * A factory for creating class invariants and operation contracts from DL
 * specifications. For an example, see java_dl/DLContractChooser.
 */
public final class DLSpecFactory {
    private final Services services;
        

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public DLSpecFactory(Services services) {
	assert services != null;
	this.services = services;
    }

    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Term extractPre(Term fma) throws ProofInputException {
	if(!fma.op().equals(Junctor.IMP)) {
	    throw new ProofInputException("Implication expected");
	} else {
	    return fma.sub(0);
	}
    }
    
    
    private LocationVariable extractHeapAtPre(Term fma) 
    		throws ProofInputException {
	if(fma.sub(1).op() instanceof UpdateApplication) {
	    final Term update = fma.sub(1).sub(0);
	    assert update.sort() == Sort.UPDATE;
	    if(!(update.op() instanceof ElementaryUpdate)) {
		throw new ProofInputException("Elementary update expected, "
					      + "but found: " + update);
	    }
	    final ElementaryUpdate eu = (ElementaryUpdate) update.op();
	    if(!(eu.lhs() instanceof ProgramVariable)) {
		throw new ProofInputException("Program variable expected, "
				              + "but found: " + eu.lhs());
	    } else if(!update.sub(0).equals(services.getTermBuilder().getBaseHeap())) {
		throw new ProofInputException("heap expected, "
					      + "but found: " + update.sub(0));
	    } else {
		return (LocationVariable) eu.lhs();
	    }
	} else {
	    return null;
	}
    }
    
    
    private ProgramVariable extractExcVar(Term fma) {
	final Term modFma = fma.sub(1).op() instanceof UpdateApplication
	                    ? fma.sub(1).sub(1)
	                    : fma.sub(1);	
	
	final SourceElement se = modFma.javaBlock().program().getFirstElement();
	if(se instanceof CatchAllStatement) {
	    return ((CatchAllStatement) se).getParam();
	} else {
	    return null;
	}
    }

    
    private UseOperationContractRule.Instantiation extractInst(Term fma) 
    		throws ProofInputException {
	final UseOperationContractRule.Instantiation result 
		= UseOperationContractRule.computeInstantiation(fma.sub(1), 
								services);
	if(result == null) {
	    throw new ProofInputException("Contract formula of wrong shape: " 
		    	                  + fma.sub(1));
	}

	return result;
    }

    
    private IProgramMethod extractProgramMethod(
	    			UseOperationContractRule.Instantiation inst) 
    		throws ProofInputException {
	return inst.pm;
    }

    
    private Modality extractModality(
	    			UseOperationContractRule.Instantiation inst) 
    		throws ProofInputException {
	return inst.mod;
    }
    
    
    private ProgramVariable extractSelfVar(
    				UseOperationContractRule.Instantiation inst) 
    		throws ProofInputException {
	if(inst.actualSelf == null) {
	    assert inst.pm.isStatic();
	    return null;
	} else if(inst.actualSelf.op() instanceof ProgramVariable) {
	    return (ProgramVariable) inst.actualSelf.op();
	} else {
	    throw new ProofInputException("Program variable expected, "
		    			  + "but found: " + inst.actualSelf);
	}
    }
    

    private ImmutableList<ProgramVariable> extractParamVars(
	    			UseOperationContractRule.Instantiation inst) 
	    	throws ProofInputException {
	ImmutableList<ProgramVariable> result 
		= ImmutableSLList.<ProgramVariable> nil();	
	for(Term param : inst.actualParams) {
	    if(param.op() instanceof ProgramVariable) {
		result = result.append((ProgramVariable) param.op());
	    } else {
		throw new ProofInputException("Program variable expected, "
					      + "but found: " + param);
	    }
	}
	return result;
    }

    
    private ProgramVariable extractResultVar(
	    			UseOperationContractRule.Instantiation inst) 
	    	throws ProofInputException {
	if(inst.actualResult == null) {
	    return null;
	} else if(inst.actualResult instanceof ProgramVariable) {
	    return (ProgramVariable) inst.actualResult;
	} else {
	    throw new ProofInputException("Program variable expected, "
		   		          + "but found: " + inst.actualResult);
	}
    }
    

    private Term extractPost(Term fma) {
	final Term modFma = fma.sub(1).op() instanceof UpdateApplication
	                    ? fma.sub(1).sub(1)
	                    : fma.sub(1);
	return modFma.sub(0);
    }
    
    
    

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    /**
     * Creates a class invariant from a formula and a designated "self".
     */
    public ClassInvariant createDLClassInvariant(String name,
	    					 String displayName, 
	    					 ParsableVariable selfVar, 
	    					 Term inv)
	    throws ProofInputException {
	assert name != null;
	if(displayName == null) {
	    displayName = name;
	}
	assert selfVar != null;
	assert inv != null;

	final KeYJavaType kjt 
		= services.getJavaInfo().getKeYJavaType(selfVar.sort());
	assert kjt != null;

	return new ClassInvariantImpl(name, 
				      displayName, 
				      kjt,
				      new Private(),
				      inv, 
				      selfVar);
    }

    
    /**
     * Creates an operation contract from an implication formula of the form
     *  "pre -> {heapAtPre := heap}
     *                [#catchAll(java.lang.Throwable exc){m();}]post",
     * (where the update and/or the #catchAll may be omitted) and a modifies 
     * clause.
     */
    public FunctionalOperationContract createDLOperationContract(String name, 
	    					       Term fma, 
	    					       Term modifies)
	    throws ProofInputException {
	assert name != null;
	assert fma != null;
	assert modifies != null;
	
	final ContractFactory cf = new ContractFactory(services);

	//extract parts of fma
	final Term pre = extractPre(fma);
	LocationVariable heapAtPreVar = extractHeapAtPre(fma);
	ProgramVariable excVar = extractExcVar(fma);	
	final UseOperationContractRule.Instantiation inst = extractInst(fma);
	final IProgramMethod pm = extractProgramMethod(inst);
	final Modality modality = extractModality(inst);
	final ProgramVariable selfVar = pm.isConstructor() 
	                                ? extractResultVar(inst) 
	                                : extractSelfVar(inst);
	final ImmutableList<ProgramVariable> paramVars = extractParamVars(inst);
	ProgramVariable resultVar = pm.isConstructor() 
		                    ? null
		                    : extractResultVar(inst);
	Term post = extractPost(fma);
	
	//heapAtPre must not occur in precondition or in modifies clause
	if(heapAtPreVar != null) {
	    final OpCollector oc = new OpCollector();
	    pre.execPostOrder(oc);
	    modifies.execPostOrder(oc);
	    if(oc.contains(heapAtPreVar)) {
		throw new ProofInputException(
		    "variable \"" + heapAtPreVar + "\" used for pre-state heap" 
		    + " must not occur in precondition or in modifies clause");
	    }
	}
	
	HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	//heapAtPre variable may be omitted
	TermBuilder tb = services.getTermBuilder();
	if(heapAtPreVar == null) {
	    heapAtPreVar = tb.heapAtPreVar(heapLDT.getHeap() + "AtPre", heapLDT.getHeap().sort(), false);
	}
        Map<LocationVariable,LocationVariable> atPreVars = new LinkedHashMap<LocationVariable, LocationVariable>();
        atPreVars.put(heapLDT.getHeap(), heapAtPreVar);
        Map<LocationVariable,Term> mods = new LinkedHashMap<LocationVariable,Term>();
        mods.put(heapLDT.getHeap(), modifies);

	//result variable may be omitted
	if(resultVar == null && !pm.isVoid()) {
	    resultVar = tb.resultVar(pm, false);
	}

	//exception variable may be omitted
	if(excVar == null) {
	    excVar = tb.excVar(pm, false);
	    Term excNullTerm = tb.equals(tb.var(excVar), tb.NULL());
	    if(modality == Modality.DIA) {
		post = tb.and(post, excNullTerm);
	    } else if(modality == Modality.BOX) {
		post = tb.or(post, tb.not(excNullTerm));
	    } else {
		throw new ProofInputException(
		        "unknown semantics for exceptional termination: "
		                + modality + "; please use #catchAll block");
	    }
	}

        Map<LocationVariable,Term> pres = new LinkedHashMap<LocationVariable,Term>();
        pres.put(heapLDT.getHeap(), pre);

        Map<LocationVariable,Term> posts = new LinkedHashMap<LocationVariable,Term>();
        posts.put(heapLDT.getHeap(), post);
      	
        Map<LocationVariable,Boolean> hasMod = new LinkedHashMap<LocationVariable, Boolean>();
        hasMod.put(heapLDT.getHeap(), true);
        hasMod.put(heapLDT.getSavedHeap(), true);
        
	final boolean isLibraryClass 
		= ((TypeDeclaration)pm.getContainerType() 
			              .getJavaType()).isLibraryClass();
	return cf.func(name,
					 pm.getContainerType(),		
					 pm, 
					 modality, 
					 pres,
					 null,// TODO measured_by in DL contracts not supported yet
					 posts,
					 null, // TODO no model methods in DL contracts
					 mods,
					 new LinkedHashMap<ProgramVariable,Term>(),
					 hasMod, // TODO strictly pure in DL contracts not supported yet
					 selfVar, 
					 paramVars, 
					 resultVar, 
					 excVar,
					 atPreVars,
					 !isLibraryClass);
    }
}