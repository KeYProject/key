// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.dl.translation;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.*;


/**
 * A factory for creating class invariants and operation contracts from DL
 * specifications.
 */
public final class DLSpecFactory {

    private static final TermBuilder TB = TermBuilder.DF;
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
    
    
    private ProgramVariable extractHeapAtPre(Term fma) 
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
	    } else if(!update.sub(0).equals(TB.heap(services))) {
		throw new ProofInputException("heap expected, "
					      + "but found: " + update.sub(0));
	    } else {
		return (ProgramVariable) eu.lhs();
	    }
	} else {
	    return null;
	}
    }
    

    private MethodBodyStatement extractMBS(Term fma) 
    		throws ProofInputException {
	final Term modFma = fma.sub(1).op() instanceof UpdateApplication
	                    ? fma.sub(1).sub(1)
	                    : fma.sub(1);
	if(!(modFma.op() instanceof Modality)) {
	    throw new ProofInputException("Modality expected, "
		                          + "but found: " + modFma);
	}
	
	final SourceElement se 
		= modFma.javaBlock().program().getFirstElement();
	if(se instanceof CatchAllStatement) {
	    final CatchAllStatement cas = (CatchAllStatement) se;
	    final SourceElement body = cas.getBody().getFirstElement();
	    return (MethodBodyStatement) body;
	} else {
	    return (MethodBodyStatement) se;
	}
    }

    
    private ProgramMethod extractProgramMethod(MethodBodyStatement mbs) {
	return mbs.getProgramMethod(services);
    }

    
    private ProgramVariable extractSelfVar(MethodBodyStatement mbs) {
	return mbs.isStatic(services)  
	       ? null 
	       : (ProgramVariable) mbs.getDesignatedContext();
    }
    

    private ImmutableList<ProgramVariable> extractParamVars(
	    					MethodBodyStatement mbs) {
	final ImmutableArray<Expression> args = mbs.getArguments();

	ImmutableList<ProgramVariable> result 
		= ImmutableSLList.<ProgramVariable> nil();
	for(int i = args.size() - 1; i >= 0; i--) {
	    result = result.prepend((ProgramVariable) args.get(i));
	}

	return result;
    }

    
    private ProgramVariable extractResultVar(MethodBodyStatement mbs) {
	return (ProgramVariable) mbs.getResultVariable();
    }
    

    private ProgramVariable extractExcVar(Term fma) {
	final Term modFma = fma.sub(1).op() instanceof UpdateApplication
	                    ? fma.sub(1).sub(1)
	                    : fma.sub(1);	
	
	final SourceElement se = modFma.javaBlock().program().getFirstElement();
	if(se instanceof CatchAllStatement) {
	    final CatchAllStatement cas = (CatchAllStatement) se;
	    return (ProgramVariable) cas.getParameterDeclaration()
		                        .getVariableSpecification()
		                        .getFirstElement();
	} else {
	    return null;
	}
    }

    
    private Modality extractModality(Term fma) {
	final Term modFma = fma.sub(1).op() instanceof UpdateApplication
	                    ? fma.sub(1).sub(1)
	                    : fma.sub(1);
	
	return (Modality) modFma.op();
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
     *                [#catchAll(java.lang.Exception exc){m();}]post",
     * (where the update and/or the #catchAll may be omitted) and a modifies 
     * clause.
     */
    public OperationContract createDLOperationContract(String name, 
	    					       Term fma, 
	    					       Term modifies)
	    throws ProofInputException {
	assert name != null;
	assert fma != null;
	assert modifies != null;

	//extract parts of fma
	MethodBodyStatement mbs = extractMBS(fma);
	if(mbs.getProgramMethod(services) == null) {
	    throw new ProofInputException("method \""
		    + mbs.getMethodReference() + "\" not found");
	}
	ProgramMethod pm = extractProgramMethod(mbs);
	Modality modality = extractModality(fma);
	Term pre = extractPre(fma);
	Term post = extractPost(fma);
	ProgramVariable selfVar = extractSelfVar(mbs);
	ImmutableList<ProgramVariable> paramVars = extractParamVars(mbs);
	ProgramVariable resultVar = extractResultVar(mbs);
	ProgramVariable excVar = extractExcVar(fma);
	ProgramVariable heapAtPreVar = extractHeapAtPre(fma);
	
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
	
	//heapAtPre variable may be omitted
	if(heapAtPreVar == null) {
	    heapAtPreVar = TB.heapAtPreVar(services, "heapAtPre", false);
	}

	//result variable may be omitted
	if(resultVar == null && pm.getKeYJavaType() != null) {
	    resultVar = TB.resultVar(services, pm, false);
	}

	//exception variable may be omitted
	if(excVar == null) {
	    excVar = TB.excVar(services, pm, false);
	    Term excNullTerm = TB.equals(TB.var(excVar), TB.NULL(services));
	    if(modality == Modality.DIA) {
		post = TB.and(post, excNullTerm);
	    } else if(modality == Modality.BOX) {
		post = TB.or(post, TB.not(excNullTerm));
	    } else {
		throw new ProofInputException(
		        "unknown semantics for exceptional termination: "
		                + modality + "; please use #catchAll block");
	    }
	}

	return new OperationContractImpl(name,
					 pm.getContainerType(),		
					 pm, 
					 modality, 
					 pre,
					 null,//measured_by in DL contracts not supported yet					 
					 post, 
					 modifies, 
					 selfVar, 
					 paramVars, 
					 resultVar, 
					 excVar,
					 TB.var(heapAtPreVar));
    }
}
