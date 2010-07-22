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

import java.util.*;

import de.uka.ilkd.key.java.*;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
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
    
    
    private ParsableVariable extractSelfVar(MethodBodyStatement mbs) {
        return mbs.isStatic(services) 
               ? null 
               : (ProgramVariable) mbs.getDesignatedContext();
    }
    
    
    private ImmutableList<ParsableVariable> extractParamVars(MethodBodyStatement mbs) {
        ImmutableArray<Expression> args = mbs.getArguments();
        
        ImmutableList<ParsableVariable> result = ImmutableSLList.<ParsableVariable>nil();
        for(int i = args.size() - 1; i >= 0; i--) {
            result = result.prepend((ProgramVariable) args.get(i));
        }
        
        return result;
    }
    
    
    private ParsableVariable extractResultVar(MethodBodyStatement mbs) {
        return (ProgramVariable) mbs.getResultVariable();
    }
    
    
    private ParsableVariable extractExcVar(Term fma) {
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
    
    
    private Map<Operator, Function>
        extractAtPreFunctions(Term term) {
        Map<Operator, Function> result = new LinkedHashMap<Operator, Function>();
        
        //is the operator of the passed term an atPre function?
        Operator op = term.op();
        String nameString = op.name().toString();
        if(nameString.endsWith("@pre")) {
            assert op instanceof Function;
            
            //retrieve operator corresponding to the atPre function
            Name normalName 
                = new Name(nameString.substring(0, nameString.length() - 4));
            Operator normalOp = (Operator) services.getNamespaces()
                                                   .lookup(normalName);
            if(normalOp == null) {
                ProgramVariable attrPV 
                        = services.getJavaInfo()
                                  .getAttribute(normalName.toString());
                assert attrPV != null;
                normalOp = AttributeOp.getAttributeOp(attrPV);
            }
            assert normalOp != null;
            
            //add pair to map
            result.put(normalOp, (Function)op);
        }
        
        //recurse to subterms
        for(int i = 0; i < term.arity(); i++) {
            Map<Operator, Function> map = extractAtPreFunctions(term.sub(i));
            result.putAll(map);
        }
        
        return result;
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
                                            ImmutableSet<LocationDescriptor> modifies) 
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
        ParsableVariable selfVar         = extractSelfVar(mbs);
        ImmutableList<ParsableVariable> paramVars = extractParamVars(mbs);
        ParsableVariable resultVar       = extractResultVar(mbs);
        ParsableVariable excVar          = extractExcVar(fma);
        Map<Operator, Function> atPreFunctions = extractAtPreFunctions(post.getFormula());
        
        //atPre-functions may not occur in precondition
        Map<Operator, Function> forbiddenAtPreFunctions = extractAtPreFunctions(pre.getFormula());
        if(!forbiddenAtPreFunctions.isEmpty()) {
            throw new ProofInputException(
                "@pre-function not allowed in precondition: " 
                + forbiddenAtPreFunctions.values().iterator().next());
        }
        
        //atPre-functions may not occur in modifier set
        for (LocationDescriptor modify : modifies) {
            LocationDescriptor loc = modify;
            if (loc instanceof BasicLocationDescriptor) {
                BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
                Term formula = bloc.getFormula();
                Term locTerm = bloc.getLocTerm();
                forbiddenAtPreFunctions = new LinkedHashMap<Operator, Function>();
                forbiddenAtPreFunctions.putAll(extractAtPreFunctions(formula));
                forbiddenAtPreFunctions.putAll(extractAtPreFunctions(locTerm));
                if (!forbiddenAtPreFunctions.isEmpty()) {
                    throw new ProofInputException(
                            "@pre-function not allowed in modifier set: "
                                    + forbiddenAtPreFunctions.values().iterator().next());
                }
            }
        }
        
        //result variable may be omitted
	if(resultVar == null && pm.getKeYJavaType() != null) {
	    ProgramElementName resultPEN = new ProgramElementName("res");
	    resultVar = new LocationVariable(resultPEN, pm.getKeYJavaType());
	}

        //exception variable may be omitted
	if(excVar == null) {
            excVar = SVF.createExcVar(services, pm, false);
	    Term excNullTerm = TB.equals(TB.var(excVar), TB.NULL(services));
            if(modality == Op.DIA) {
                post = post.conjoin(new FormulaWithAxioms(excNullTerm));
            } else if(modality == Op.BOX) {
                post = post.disjoin(new FormulaWithAxioms(TB.not(excNullTerm)));
            } else {
                throw new ProofInputException(
                            "unknown semantics for exceptional termination: " 
                            + modality + "; please use #catchAll block");
            }
        }
        
        TermBuilder tb = TermBuilder.DF;
        TermFactory tf = tb.tf();
        
        
        Term[] argTerms = new Term[pm.getParameterDeclarationCount()+(pm.isStatic() ? 0 : 1)];
        int j=0;
        if(!pm.isStatic()){
                argTerms[j++] = tb.var(selfVar);
        }

        for(int i=j; i<argTerms.length; i++){
            argTerms[i] = tb.var((ProgramVariable) pm.getParameterDeclarationAt(i-j).
                    getVariableSpecification().getProgramVariable());
        }
        
        Term ws = tf.createWorkingSpaceNonRigidTerm(pm,
            (Sort) services.getNamespaces().sorts().lookup(new Name("int")),
            argTerms
            );
        FormulaWithAxioms wsPost = new FormulaWithAxioms(tb.tt(), new HashMap<Operator, Term>());
        
        services.getNamespaces().functions().add(ws.op());
        
        return new OperationContractImpl(name, 
                                         displayName, 
                                         pm,
                                         modality,
                                         pre,
                                         post,
                                         wsPost,
                                         modifies,                                        
                                         ws,
                                         selfVar,
                                         paramVars,
                                         resultVar,
                                         excVar,
                                         atPreFunctions); 
    }
}
