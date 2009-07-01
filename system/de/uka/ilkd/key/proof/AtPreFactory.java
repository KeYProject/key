// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.updatesimplifier.Update;



public class AtPreFactory {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    public static final AtPreFactory INSTANCE = new AtPreFactory();
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------    
    
    private AtPreFactory() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * Returns an available name constructed by affixing a counter to the passed 
     * base name.
     */
    public String getNewName(String baseName, 
                              Services services, 
                              List<String> locallyUsedNames) {
        NamespaceSet namespaces = services.getNamespaces();
            
        int i = 0;
        String result;
        do {
            result = baseName + "_" + i++;
        } while(namespaces.lookup(new Name(result)) != null
                || locallyUsedNames.contains(result));
        
        return result;
    }
    
    
    /**
     * Returns the sort of the passed operator.
     */
    private Sort getSort(Operator op) {
        return op.sort(null);
    }
    
    
    /**
     * Returns the argument sorts of the passed operator 
     * (why is that so complicated?).
     */
    private ArrayOfSort getArgSorts(Operator op, Services services) {
        if(op instanceof Function) {
            return ((Function)op).argSort();
        } else if(op instanceof ProgramVariable && op.arity() == 0) {
            return new ArrayOfSort();
        } else {
            assert false : "unexpected operator: " + op.name() 
                            + " (" + op.getClass() + ")";
            return null;
        }
    }
    
    
    /**
     * Helper for buildAtPreDefinition().
     */
    private Term[] getTerms(ArrayOfQuantifiableVariable vars) {
        int numVars = vars.size();
        Term[] result = new Term[numVars];

        for(int i = 0; i < numVars; i++) {
            LogicVariable var
                    = (LogicVariable)(vars.getQuantifiableVariable(i));
            result[i] = TB.var(var);
        }

        return result;
    }
    
    

    private Function createAtPreFunction(Operator normalOp, 
                                         Services services,
                                         List<String> locallyUsedNames) {
        String baseName = normalOp.name() instanceof ProgramElementName
                   ? ((ProgramElementName)normalOp.name()).getProgramName()
                   : normalOp.name().toString();
        
        if (baseName.startsWith("<") && baseName.endsWith(">")) {
            baseName = baseName.substring(1, baseName.length() - 1);
        } else if(baseName.startsWith(".")) {
            baseName = baseName.substring(1);
        }
        
        baseName = baseName + "AtPre";
        String uniqueName = getNewName(baseName, services, locallyUsedNames);

        assert false;
        Function result=null; 
//            = new NonRigidFunctionLocation(new Name(uniqueName),
//                                           getSort(normalOp),
//                                           getArgSorts(normalOp, 
//                                                       services), false);
        return result;
    }
    
    
    /**
     * Creates atPre-functions for all relevant operators in the passed term.
     */
    public void createAtPreFunctionsForTerm(
            Term term,
            /*inout*/ Map<Operator,Function/*atPre*/> atPreFunctions,
            Services services,
            List<String> locallyUsedNames) {
        int arity = term.arity();
        Sort[] subSorts = new Sort[arity];
        for(int i = 0; i < arity; i++) {
            Term subTerm = term.sub(i);
            createAtPreFunctionsForTerm(subTerm, 
                                        atPreFunctions, 
                                        services, 
                                        locallyUsedNames);
            subSorts[i] = subTerm.sort();
        }

        if(term.op() instanceof ProgramVariable
           || term.op() instanceof ProgramMethod) {
            Function atPreFunc = atPreFunctions.get(term.op());
            if(atPreFunc == null) {
                atPreFunc = createAtPreFunction(term.op(), 
                                                services, 
                                                locallyUsedNames);
                atPreFunctions.put(term.op(), atPreFunc);
                locallyUsedNames.add(atPreFunc.name().toString());
            }
        }
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------    
    
    /**
     * Creates an atPre-function for the passed operator, i.e., a new function
     * symbol with the same signature.
     */
    public Function createAtPreFunction(Operator normalOp, Services services) {
        return createAtPreFunction(normalOp, 
                                   services, 
                                   new LinkedList<String>());
    }
    
    
    /**
     * Creates atPre-functions for all relevant operators in the passed term.
     */
    public void createAtPreFunctionsForTerm(
            Term term,
            /*inout*/ Map<Operator,Function/*atPre*/> atPreFunctions,
            Services services) {
        createAtPreFunctionsForTerm(term,
                                    atPreFunctions,
                                    services,
                                    new LinkedList<String>());
    }

    

    /**
     * Creates a definition for an atPre function.
     */
    public Update createAtPreDefinition(Operator normalOp, 
                                        Function atPreFunc,
                                        Services services) {
        assert normalOp != null;
        assert atPreFunc != null;
        
        int arity = normalOp.arity();
        assert arity == atPreFunc.arity();
        LogicVariable[] args = new LogicVariable[arity];
        if(arity == 1) {
            args[0] = new LogicVariable(new Name("x"), atPreFunc.argSort(0));
        } else {
            for(int i = 0; i < arity; i++) {
                args[i] = new LogicVariable(new Name("x" + i), atPreFunc.argSort(i));
            }
        }
    
        Term[] argTerms = getTerms(new ArrayOfQuantifiableVariable(args));
        Term atPreTerm = TB.func(atPreFunc, argTerms);        
        Term normalTerm = TermFactory.DEFAULT.createTerm(
                                    normalOp,
                                    argTerms,
                                    null,
                                    null);
        
        UpdateFactory uf = new UpdateFactory(services, new UpdateSimplifier());
        Update result = uf.quantify(args,
                                    uf.elementaryUpdate(atPreTerm, normalTerm));
        
        return result;
    }
    
    
    /**
     * Creates definitions for a set of atPre functions.
     */
    public Update createAtPreDefinitions(
         /*in*/ Map<Operator,Function/*atPre*/> atPreFunctions, 
         Services services) {
        assert atPreFunctions != null;
        
        UpdateFactory uf = new UpdateFactory(services, new UpdateSimplifier());
        Update result = uf.skip();
        
        for(Map.Entry<Operator,Function> entry : atPreFunctions.entrySet()) {
            Operator normalOp = entry.getKey();
            Function atPreFunc = entry.getValue();
            Update def = createAtPreDefinition(normalOp, atPreFunc, services);
            result = uf.parallel(result, def);
        }
        
        return result;
    }
}
