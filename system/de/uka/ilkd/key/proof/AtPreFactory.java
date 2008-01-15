// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.AccessOp;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.AttributeOp;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.NonRigidFunctionLocation;
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
    private String getNewName(String baseName, Services services) {
        NamespaceSet namespaces = services.getNamespaces();
            
        int i = 0;
        String result;
        do {
            result = baseName + "_" + i++;
        } while(namespaces.lookup(new Name(result)) != null);
        
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
        } else if(op instanceof AttributeOp) {
            AttributeOp aop = (AttributeOp) op;
            
            //HACK: Oddly, the length attribute is contained in a kjt "(SuperArray, null)",
            //i.e. its argument does not have a sort. Therefore, we have to treat this case 
            //separately.
            if(aop.attribute().equals(services.getJavaInfo()
                                              .getArrayLength())) {
                Sort objectSort 
                    = services.getJavaInfo().getJavaLangObjectAsSort();
                return new ArrayOfSort(new Sort[]{objectSort});
            }
            
            Sort selfSort = aop.getContainerType().getSort();            
            assert selfSort != null;
            Sort[] argSorts = new Sort[] {selfSort};
            return new ArrayOfSort(argSorts);
        } else if(op instanceof ArrayOp) {
            ArrayOp aop = (ArrayOp) op;
            Sort[] argSorts = new Sort[] {aop.arraySort(), 
                                          services.getTypeConverter()
                                                  .getIntLDT()
                                                  .targetSort()};
            return new ArrayOfSort(argSorts);
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
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------    
    
    /**
     * Creates an atPre-function for the passed operator, i.e., a new function
     * symbol with the same signature.
     */
    public Function createAtPreFunction(Operator normalOp, Services services) {
        String atPreName = normalOp.name().toString() + "AtPre";
        if(atPreName.startsWith(".")) {
            atPreName = atPreName.substring(1);
        }
        
        Function result 
            = new NonRigidFunctionLocation(new Name(getNewName(atPreName, 
                                                               services)),
                                           getSort(normalOp),
                                           getArgSorts(normalOp, 
                                                       services));
        return result;
    }
    
    
    /**
     * Creates atPre-functions for all relevant operators in the passed term.
     */
    public void createAtPreFunctionsForTerm(
                            Term term,
                            /*inout*/ Map /*Operator (normal) 
                            -> Function (atPre)*/ atPreFunctions,
                            Services services) {
        int arity = term.arity();
        Sort[] subSorts = new Sort[arity];
        for(int i = 0; i < arity; i++) {
            Term subTerm = term.sub(i);
            createAtPreFunctionsForTerm(subTerm, atPreFunctions, services);
            subSorts[i] = subTerm.sort();
        }

        if(term.op() instanceof AccessOp
           || term.op() instanceof ProgramVariable
           || term.op() instanceof ProgramMethod) {
            Function atPreFunc = (Function)(atPreFunctions.get(term.op()));
            if(atPreFunc == null) {
                atPreFunc = AtPreFactory.INSTANCE.createAtPreFunction(term.op(), 
                                                                      services);
                atPreFunctions.put(term.op(), atPreFunc);
            }
        }
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
                                    (ArrayOfQuantifiableVariable)null,
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
         /*in*/ Map /*Operator (normal) -> Function (atPre)*/ atPreFunctions, 
         Services services) {
        assert atPreFunctions != null;
        
        UpdateFactory uf = new UpdateFactory(services, new UpdateSimplifier());
        Update result = uf.skip();
        
        Iterator it = atPreFunctions.entrySet().iterator();
        while(it.hasNext()) {
            Map.Entry entry = (Map.Entry) it.next();
            Operator normalOp = (Operator) entry.getKey();
            Function atPreFunc = (Function) entry.getValue();
            Update def = createAtPreDefinition(normalOp, atPreFunc, services);
            result = uf.parallel(result, def);
        }
        
        return result;
    }
}
