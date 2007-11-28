// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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

package de.uka.ilkd.key.parser.ocl;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IteratorOfLogicVariable;
import de.uka.ilkd.key.logic.op.IteratorOfParsableVariable;
import de.uka.ilkd.key.logic.op.ListOfLogicVariable;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.sort.ObjectSort;


/**
 * Resolves property calls of any kind. 
 * Keeps a stack of namespaces to deal with several levels of local variables 
 * (e.g. "self", or iterator variables in forall() or select() subtrees).
 */
class PropertyManager {
    
    private static final TermBuilder tb = TermBuilder.DF;
    
    private final JavaInfo javaInfo;
    private final ListOfPropertyResolver resolvers;
    
    private ListOfNamespace /*ParsableVariable*/
            localVariablesNamespaces = SLListOfNamespace.EMPTY_LIST;
    
    
    public PropertyManager(Services services, FormulaBoolConverter fbc, ParsableVariable excVar) {
        this.javaInfo = services.getJavaInfo();
        ListOfPropertyResolver list = SLListOfPropertyResolver.EMPTY_LIST;
        list = list.prepend(new AssociationResolver(services));
        list = list.prepend(new BuiltInPropertyResolver(services, excVar));
        list = list.prepend(new MethodResolver(services, fbc));
        list = list.prepend(new AttributeResolver(services));
        resolvers = list;
    }
    
    
    /**
     * Tries to resolve a name as a property call on an explicit receiver.
     * @throws OCLTranslationError 
     */
    private OCLEntity resolveExplicit(OCLEntity receiver,
                                      String name,
                                      OCLParameters parameters) throws OCLTranslationError {
        IteratorOfPropertyResolver it = resolvers.iterator();
        while(it.hasNext()) {
            OCLEntity result = it.next().resolve(receiver, name, parameters);
            if(result != null) {
                return result;
            }
        }
        return null;
    }
    

    /**
     * Tries to resolve a name as a type.
     */
    private OCLEntity resolveType(String name) {
        try {
            KeYJavaType kjt = javaInfo.getTypeByClassName(name);
            if(kjt != null) {
                return new OCLEntity(kjt);
            }
        } catch(RuntimeException e) {
        	// do nothing
        }
        return null;
    }
    
    
    /**
     * Tries to resolve a name as a local variable.
     */
    private OCLEntity resolveLocal(String name) {
        Name n = new Name(name);
        IteratorOfNamespace it = localVariablesNamespaces.iterator();
        while(it.hasNext()) {   
            ParsableVariable localVar = (ParsableVariable) it.next().lookup(n);
            if(localVar != null) {
                Term varTerm = tb.var(localVar);
                return new OCLEntity(varTerm);
            }
        }
        
        return null;
    }
    
        
    /**
     * Tries to resolve a name as a property call on any available implicit 
     * receiver.
     * @throws OCLTranslationError 
     */
    private OCLEntity resolveImplicit(String name, OCLParameters parameters) throws OCLTranslationError {
        IteratorOfNamespace it = localVariablesNamespaces.iterator();
        while(it.hasNext()) {
            Namespace ns = it.next();
            ListOfNamed elements = ns.elements();
            
            IteratorOfNamed it2 = elements.iterator();
            while(it2.hasNext()) {
        	ParsableVariable localVar = (ParsableVariable) it2.next();
                if(localVar.sort() instanceof ObjectSort) {              
                    Term recTerm = tb.var(localVar);
                    OCLEntity result 
                           = resolveExplicit(new OCLEntity(recTerm), 
                                            name,
                                            parameters);
                    if(result != null) {
                        return result;
                    }
                }
            }
        }
        
        return null;
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
        IteratorOfLogicVariable it = pvs.iterator();
        while(it.hasNext()) {
            localVariablesNamespaces.head().addSafely(it.next());
        }
    }
    
    
    /**
     * Throws away the topmost namespace on the stack.
     */
    public void popLocalVariablesNamespace() {
        localVariablesNamespaces = localVariablesNamespaces.tail();
    }
    
    
    /**
     * Determines whether a variable has to be put into localVariableNamespace
     * @param propertyName name of the propertyCall
     * @return true, if propertyName needs a variable to be put into
     * localVariableNamespace
     */
    public boolean needVarDeclaration(String propertyName) {
        IteratorOfPropertyResolver it = resolvers.iterator();
        while(it.hasNext()) {
            if (it.next().needVarDeclaration(propertyName)) {
                return true;
            }
        }
        return false;
    }
    
    
    /**
     * Resolves arbitrary property calls.
     * @param receiver the specified explicit receiver, or null
     * @param name name of the property
     * @param parameters actual parameters of the property call, or null
     * @return corresponding term, type or collection if successful, null 
     * otherwise
     * @throws OCLTranslationError 
     */
    public OCLEntity resolve(OCLEntity receiver,
                             String name, 
                             OCLParameters parameters) throws OCLTranslationError {
        OCLEntity result = null;
        
        if(receiver != null) {
            result = resolveExplicit(receiver, name, parameters);
        } else {
            result = resolveType(name);
            if(result == null) {
                result = resolveLocal(name);
                if(result == null) {
                    result = resolveImplicit(name, parameters);
                }
            }
        }
        
        return result;
    }
}
