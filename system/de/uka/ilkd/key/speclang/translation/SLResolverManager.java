// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.translation;


import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ObjectSort;


/**
 * Resolves property calls of any kind. Keeps a list of resolvers doing the
 * actual work, and a stack of namespaces to deal with several levels of local 
 * variables (e.g. "self", or iterator variables in forall() or select() 
 * subtrees).
 */
public abstract class SLResolverManager {
    
    public final SLTranslationExceptionManager excManager;
    private static final TermBuilder TB = TermBuilder.DF;

    private ListOfSLExpressionResolver resolvers = SLListOfSLExpressionResolver.EMPTY_LIST;
    private final KeYJavaType specInClass;
    private final ParsableVariable selfVar;
    private final boolean useLocalVarsAsImplicitReceivers;
        
    private ListOfNamespace /*ParsableVariable*/
        localVariablesNamespaces = SLListOfNamespace.EMPTY_LIST;

    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    protected SLResolverManager(SLTranslationExceptionManager excManager, 
                                KeYJavaType specInClass,
                                ParsableVariable selfVar,
                                boolean useLocalVarsAsImplicitReceivers) {
        assert excManager != null;
        this.excManager = excManager;
        this.specInClass = specInClass;
        this.selfVar = selfVar;
        this.useLocalVarsAsImplicitReceivers = useLocalVarsAsImplicitReceivers;
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    protected void addResolver(SLExpressionResolver resolver) {
        assert resolver != null;
        resolvers = resolvers.append(resolver);
    }
    
    private String getShortName(String name) {
        return name.substring(name.lastIndexOf(".") + 1);
    }


    private boolean isFullyQualified(String name) {
        return name.indexOf(".") > -1;
    }

    
    /**
     * Tries to resolve a name as a local variable.
     */
    private SLExpression resolveLocal(String name) {
        Name n = new Name(name);
        for(Namespace ns : localVariablesNamespaces) {
            ParsableVariable localVar = (ParsableVariable) ns.lookup(n);
            if(localVar != null) {
                Term varTerm = TB.var(localVar);
                return createSLExpression(varTerm);
            }
        }
        
        return null;
    }

    
    /**
     * Tries to resolve a name as a property call on any available implicit 
     * receiver.
     */
    private SLExpression resolveImplicit(String name, SLParameters parameters) 
            throws SLTranslationException {
        if(useLocalVarsAsImplicitReceivers) {
            for(Namespace ns : localVariablesNamespaces) {
                for(Named n : ns.elements()) {
                    ParsableVariable localVar = (ParsableVariable) n;
                    if(localVar.sort() instanceof ObjectSort) {              
                        Term recTerm = TB.var(localVar);
                        SLExpression result 
                               = resolveExplicit(createSLExpression(recTerm), 
                                                name,
                                                parameters);
                        if(result != null) {
                            return result;
                        }
                    }
                }
            }
        } else if(selfVar != null) {
            SLExpression result
                = resolveExplicit(createSLExpression(TB.var(selfVar)), 
                                  name,
                                  parameters);

            if (result != null) {
                return result;
            }            
        }
        
        // the class where the specification is written can be an implicit type receiver
        // (e.g. for static attributes or static methods)
	if(specInClass != null) {
	    SLExpression result 
		= resolveExplicit(createSLExpression(specInClass),
                                  name,
                                  parameters);
            if(result != null) {
            	return result;
            }
        }

        return null;
    }
    

    /**
     * Tries to resolve a name as a property call on an explicitly given 
     * receiver, by calling the registered resolvers.
     */
    private SLExpression resolveExplicit(SLExpression receiver, 
                                         String name, 
                                         SLParameters params) 
            throws SLTranslationException {
        for(SLExpressionResolver resolver : resolvers) {
            SLExpression result = resolver.resolve(receiver, name, params);
            if (result != null) {
                return result;
            }
        }
       
        return null;
    }
    
    
    /**
     * Helper for resolve().
     */
    private SLExpression resolveIt(SLExpression receiver,
                                   String name, 
                                   SLParameters parameters) 
            throws SLTranslationException {
        SLExpression result = null;
        
        if(receiver != null) {
            result = resolveExplicit(receiver, name, parameters);
        } else {
            result = resolveLocal(name);
            if (result == null) {
                result = resolveImplicit(name, parameters);
            }
            if (result == null) {
                result = resolveExplicit(null, name, parameters); 
            }
        }
        
        return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    /**
     * Resolves arbitrary property calls.
     * @param receiver the specified explicit receiver, or null
     * @param name name of the property
     * @param parameters actual parameters of the property call, or null
     * @return corresponding term, type or collection if successful, null 
     * otherwise
     * @throws SLTranslationException 
     */
    public SLExpression resolve(SLExpression receiver,
                                String name, 
                                SLParameters parameters) 
            throws SLTranslationException {
        String shortName = name;
        
        if (isFullyQualified(name)) {
            SLExpression result = resolveIt(receiver, name, parameters);
            if (result != null) {
                return result;
            }
            shortName = getShortName(name);
        }
        
        return resolveIt(receiver, shortName, parameters);
    }

   

    /**
     * Pushes a new, empty namespace onto the stack.
     */
    public void pushLocalVariablesNamespace() {
        Namespace ns = new Namespace();
        localVariablesNamespaces = localVariablesNamespaces.prepend(ns);
    }
    
    
    /**
     * Puts a local variable into the topmost namespace on the stack
     */
    public void putIntoTopLocalVariablesNamespace(ParsableVariable pv) {
        localVariablesNamespaces.head().addSafely(pv);
    }
    
    
    /**
     * Puts a list of local variables into the topmost namespace on the stack. 
     */
    public void putIntoTopLocalVariablesNamespace(ListOfLogicVariable pvs) {
        for(LogicVariable pv : pvs) {
            localVariablesNamespaces.head().addSafely(pv);
        }
    }
       
    
    /**
     * Determines whether a variable has to be put into localVariableNamespace
     * @param name2BeResolved name of the element to be resolved
     * @return true, if name2BeResolved needs a variable to be put into
     * localVariableNamespace
     */
    public boolean needVarDeclaration(String name2BeResolved) {
        IteratorOfSLExpressionResolver it = resolvers.iterator();
        while(it.hasNext()) {
            if (it.next().needVarDeclaration(name2BeResolved)) {
                return true;
            }
        }
        return false;
    }
    
    
    /**
     * Throws away the topmost namespace on the stack.
     */
    public void popLocalVariablesNamespace() {
        localVariablesNamespaces = localVariablesNamespaces.tail();
    }

    
    public abstract SLExpression createSLExpression(Term t);
    public abstract SLExpression createSLExpression(KeYJavaType t);
    public abstract SLExpression createSLExpression(SLCollection t);
}
