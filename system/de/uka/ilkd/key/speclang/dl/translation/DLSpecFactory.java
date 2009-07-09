// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.dl.translation;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.ArrayOfExpression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.BasicLocationDescriptor;
import de.uka.ilkd.key.logic.IteratorOfLocationDescriptor;
import de.uka.ilkd.key.logic.LocationDescriptor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SLListOfParsableVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.ClassInvariantImpl;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.OperationContractImpl;
import de.uka.ilkd.key.speclang.SignatureVariablesFactory;


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
    
    
    private ListOfParsableVariable extractParamVars(MethodBodyStatement mbs) {
        ArrayOfExpression args = mbs.getArguments();
        
        ListOfParsableVariable result = SLListOfParsableVariable.EMPTY_LIST;
        for(int i = args.size() - 1; i >= 0; i--) {
            result = result.prepend((ProgramVariable) args.getExpression(i));
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
assert false : "not implemented";            
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
//                normalOp = AttributeOp.getAttributeOp(attrPV);
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
                                            SetOfLocationDescriptor modifies) 
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
        ListOfParsableVariable paramVars = extractParamVars(mbs);
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
        IteratorOfLocationDescriptor it = modifies.iterator();
        while(it.hasNext()) {
            LocationDescriptor loc = it.next();
            if(loc instanceof BasicLocationDescriptor) {
                BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
                Term formula = bloc.getFormula();
                Term locTerm = bloc.getLocTerm();
                forbiddenAtPreFunctions = new LinkedHashMap<Operator, Function>(); 
                forbiddenAtPreFunctions.putAll(extractAtPreFunctions(formula));
                forbiddenAtPreFunctions.putAll(extractAtPreFunctions(locTerm));
                if(!forbiddenAtPreFunctions.isEmpty()) {
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
            if(modality == Modality.DIA) {
                post = post.conjoin(new FormulaWithAxioms(excNullTerm));
            } else if(modality == Modality.BOX) {
                post = post.disjoin(new FormulaWithAxioms(TB.not(excNullTerm)));
            } else {
                throw new ProofInputException(
                            "unknown semantics for exceptional termination: " 
                            + modality + "; please use #catchAll block");
            }
        }
        
        return new OperationContractImpl(name, 
                                         displayName, 
                                         pm,
                                         modality,
                                         pre,
                                         post,
                                         modifies,
                                         selfVar,
                                         paramVars,
                                         resultVar,
                                         excVar,
                                         atPreFunctions); 
    }
}
