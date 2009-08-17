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
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.*;


/**
 * A factory for creating class invariants and operation contracts
 * from DL specifications.
 */
public class DLSpecFactory {
    
    private static final TermBuilder TB = TermBuilder.DF;
    private static final SignatureVariablesFactory SVF 
    	= SignatureVariablesFactory.INSTANCE;
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
        if(se instanceof CatchAllStatement) {
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
        return mbs.isStatic(services) 
               ? null 
               : (ProgramVariable) mbs.getDesignatedContext();
    }
    
    
    private ImmutableList<ProgramVariable> extractParamVars(MethodBodyStatement mbs) {
        ImmutableArray<Expression> args = mbs.getArguments();
        
        ImmutableList<ProgramVariable> result = ImmutableSLList.<ProgramVariable>nil();
        for(int i = args.size() - 1; i >= 0; i--) {
            result = result.prepend((ProgramVariable) args.get(i));
        }
        
        return result;
    }
    
    
    private ProgramVariable extractResultVar(MethodBodyStatement mbs) {
        return (ProgramVariable) mbs.getResultVariable();
    }
    
    
    private ProgramVariable extractExcVar(Term fma) {
        SourceElement se = fma.sub(1).javaBlock().program().getFirstElement();
        if(se instanceof CatchAllStatement) {
            CatchAllStatement cas = (CatchAllStatement) se;
            return (ProgramVariable) cas.getParameterDeclaration()
                                        .getVariableSpecification()
                                        .getFirstElement();
        } else {
            return null;
        }
    }
    
    
    private FormulaWithAxioms extractPre(Term fma) {
        return new FormulaWithAxioms(fma.sub(0));
    }
    
    
    private FormulaWithAxioms extractPost(Term fma) {
        return new FormulaWithAxioms(fma.sub(1).sub(0));
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
        
        KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(selfVar.sort());
        assert kjt != null;
        
        return new ClassInvariantImpl(name, 
                                      displayName, 
                                      kjt, 
                                      new FormulaWithAxioms(inv), 
                                      selfVar);
    }
  
    
    /**
     * Creates an operation contract from an implication formula of the form
     * <code>pre -> \<p\> post</code> and a modifies clause (which is how
     * DL contracts are currently represented in .key files).
     */
    public OperationContract createDLOperationContract(
                                            String name, 
                                            String displayName, 
                                            Term fma, 
                                            Term modifies) 
            throws ProofInputException {
        assert name != null;
        if(displayName == null) {
            displayName = name;
        }
        assert fma != null;
        assert modifies != null;
       
        //extract parts
        MethodBodyStatement mbs          = extractMBS(fma);
        if(mbs.getProgramMethod(services) == null) {
            throw new ProofInputException("method \"" 
        	                          + mbs.getMethodReference() 
        	                          + "\" not found");
        }
        ProgramMethod pm                 = extractProgramMethod(mbs);
        Modality modality                = extractModality(fma);
        FormulaWithAxioms pre            = extractPre(fma);
        FormulaWithAxioms post           = extractPost(fma);
        ProgramVariable selfVar          = extractSelfVar(mbs);
        ImmutableList<ProgramVariable> paramVars  = extractParamVars(mbs);
        ProgramVariable resultVar        = extractResultVar(mbs);
        ProgramVariable excVar           = extractExcVar(fma);
        //Term heapAtPre                   = extractAtPreFunctions(post.getFormula());
        assert false : "not implemented";
        return null;
//        
//        //atPre-functions may not occur in precondition or modifies clause
//        Map<Operator, Function> forbiddenAtPreFunctions 
//        	= extractAtPreFunctions(pre.getFormula());
//        if(!forbiddenAtPreFunctions.isEmpty()) {
//            throw new ProofInputException(
//                "@pre-function not allowed in precondition: " 
//                + forbiddenAtPreFunctions.values().iterator().next());
//        }
//        forbiddenAtPreFunctions = extractAtPreFunctions(modifies);
//        if(!forbiddenAtPreFunctions.isEmpty()) {
//            throw new ProofInputException(
//                "@pre-function not allowed in modifies clause: " 
//                + forbiddenAtPreFunctions.values().iterator().next());
//        }
//        
//        //result variable may be omitted
//	if(resultVar == null && pm.getKeYJavaType() != null) {
//	    ProgramElementName resultPEN = new ProgramElementName("res");
//	    resultVar = new LocationVariable(resultPEN, pm.getKeYJavaType());
//	}
//
//        //exception variable may be omitted
//	if(excVar == null) {
//            excVar = SVF.createExcVar(services, pm, false);
//	    Term excNullTerm = TB.equals(TB.var(excVar), TB.NULL(services));
//            if(modality == Modality.DIA) {
//                post = post.conjoin(new FormulaWithAxioms(excNullTerm));
//            } else if(modality == Modality.BOX) {
//                post = post.disjoin(new FormulaWithAxioms(TB.not(excNullTerm)));
//            } else {
//                throw new ProofInputException(
//                            "unknown semantics for exceptional termination: " 
//                            + modality + "; please use #catchAll block");
//            }
//        }
//        
//        return new OperationContractImpl(name, 
//                                         displayName, 
//                                         pm,
//                                         modality,
//                                         pre,
//                                         post,
//                                         modifies,
//                                         selfVar,
//                                         paramVars,
//                                         resultVar,
//                                         excVar,
//                                         heapAtPre); 
    }
}
