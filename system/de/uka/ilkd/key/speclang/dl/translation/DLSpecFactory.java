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
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
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

    private MethodBodyStatement extractMBS(Term fma) {
	SourceElement se = fma.sub(1).javaBlock().program().getFirstElement();
	if (se instanceof CatchAllStatement) {
	    CatchAllStatement cas = (CatchAllStatement) se;
	    SourceElement body = cas.getBody().getFirstElement();
	    return (MethodBodyStatement) body;
	} else {
	    return (MethodBodyStatement) se;
	}
    }

    private ProgramMethod extractProgramMethod(MethodBodyStatement mbs) {
	return mbs.getProgramMethod(services);
    }

    private Modality extractModality(Term fma) {
	return (Modality) fma.sub(1).op();
    }

    private ProgramVariable extractSelfVar(MethodBodyStatement mbs) {
	return mbs.isStatic(services) ? null : (ProgramVariable) mbs
	        .getDesignatedContext();
    }

    private ImmutableList<ProgramVariable> extractParamVars(
	    MethodBodyStatement mbs) {
	ImmutableArray<Expression> args = mbs.getArguments();

	ImmutableList<ProgramVariable> result = ImmutableSLList
	        .<ProgramVariable> nil();
	for (int i = args.size() - 1; i >= 0; i--) {
	    result = result.prepend((ProgramVariable) args.get(i));
	}

	return result;
    }

    private ProgramVariable extractResultVar(MethodBodyStatement mbs) {
	return (ProgramVariable) mbs.getResultVariable();
    }

    private ProgramVariable extractExcVar(Term fma) {
	SourceElement se = fma.sub(1).javaBlock().program().getFirstElement();
	if (se instanceof CatchAllStatement) {
	    CatchAllStatement cas = (CatchAllStatement) se;
	    return (ProgramVariable) cas.getParameterDeclaration()
		    .getVariableSpecification().getFirstElement();
	} else {
	    return null;
	}
    }

    private Term extractHeapAtPre(Term t) {
	if (t.op().name().toString().equals("heapAtPre")) {// XXX
	    return t;
	} else {
	    for (Term sub : t.subs()) {
		Term result = extractHeapAtPre(sub);
		if (result != null) {
		    return result;
		}
	    }
	}
	return null;
    }

    private Term extractPre(Term fma) {
	return fma.sub(0);
    }

    private Term extractPost(Term fma) {
	return fma.sub(1).sub(0);
    }
    
    

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    /**
     * Creates a class invariant from a formula and a designated "self".
     */
    public ClassInvariant createDLClassInvariant(String name,
	    String displayName, ParsableVariable selfVar, Term inv)
	    throws ProofInputException {
	assert name != null;
	if (displayName == null) {
	    displayName = name;
	}
	assert selfVar != null;
	assert inv != null;

	KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(selfVar.sort());
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
     * <code>pre -> \<p\> post</code> and a modifies clause (which is how DL
     * contracts are currently represented in .key files).
     */
    public OperationContract createDLOperationContract(String name, 
	    					       Term fma, 
	    					       Term modifies)
	    throws ProofInputException {
	assert name != null;
	assert fma != null;
	assert modifies != null;

	//extract parts
	MethodBodyStatement mbs = extractMBS(fma);
	if (mbs.getProgramMethod(services) == null) {
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
	Term heapAtPre = extractHeapAtPre(post);

	//atPre-functions may not occur in precondition or modifies clause
	Term forbiddenHeapAtPre = extractHeapAtPre(pre);
	if (forbiddenHeapAtPre != null) {
	    throw new ProofInputException(
		    "@pre-function not allowed in precondition: "
		            + forbiddenHeapAtPre);
	}
	forbiddenHeapAtPre = extractHeapAtPre(modifies);
	if (forbiddenHeapAtPre != null) {
	    throw new ProofInputException(
		    "@pre-function not allowed in modifies clause: "
		            + forbiddenHeapAtPre);
	}

	//result variable may be omitted
	if (resultVar == null && pm.getKeYJavaType() != null) {
	    ProgramElementName resultPEN = new ProgramElementName("res");
	    resultVar = new LocationVariable(resultPEN, pm.getKeYJavaType());
	}

	//exception variable may be omitted
	if (excVar == null) {
	    excVar = TB.excVar(services, pm, false);
	    Term excNullTerm = TB.equals(TB.var(excVar), TB.NULL(services));
	    if (modality == Modality.DIA) {
		post = TB.and(post, excNullTerm);
	    } else if (modality == Modality.BOX) {
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
					 post, 
					 modifies, 
					 null,
					 selfVar, 
					 paramVars, 
					 resultVar, 
					 excVar,
					 heapAtPre);
    }
}
