package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.IteratorOfNamespace;
import de.uka.ilkd.key.logic.ListOfNamed;
import de.uka.ilkd.key.logic.ListOfNamespace;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.SLListOfNamespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IteratorOfLogicVariable;
import de.uka.ilkd.key.logic.op.ListOfLogicVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.util.Debug;

public abstract class SLResolverManager {

    
    private static final TermBuilder tb = TermBuilder.DF;

    protected final JavaInfo javaInfo;
    
    protected ListOfNamespace /*ParsableVariable*/
        localVariablesNamespaces = SLListOfNamespace.EMPTY_LIST;

    protected ListOfSLExpressionResolver
        resolvers = SLListOfSLExpressionResolver.EMPTY_LIST;

    protected final KeYJavaType specInClass;
    protected final SLTranslationExceptionManager excManager;
    
    protected SLResolverManager(JavaInfo javaInfo,
            KeYJavaType specInClass,
            SLTranslationExceptionManager eManager,
           boolean typeResolver, 
           boolean methodResolver,
           boolean attributeResolver) {
        
        Debug.assertTrue(javaInfo != null);
        this.javaInfo = javaInfo;
        this.specInClass = specInClass;
        this.excManager = eManager;
        
        if (typeResolver) {
            resolvers = resolvers.prepend(new SLTypeResolver(javaInfo, this));            
        }
        
        if (methodResolver) {
            resolvers = resolvers.prepend(new SLMethodResolver(javaInfo, this));
        }
        
        if (attributeResolver) {
            resolvers = resolvers.prepend(new SLAttributeResolver(javaInfo, this));
        }
    }
    
    
    /**
     * Tries to resolve a name as a local variable.
     */
    private SLExpression resolveLocal(String name) {
        Name n = new Name(name);
        IteratorOfNamespace it = localVariablesNamespaces.iterator();
        while(it.hasNext()) {   
            ParsableVariable localVar = (ParsableVariable) it.next().lookup(n);
            if(localVar != null) {
                Term varTerm = tb.var(localVar);
                return createSLExpression(varTerm);
            }
        }
        
        return null;
    }

    
    /**
     * Tries to resolve a name as a property call on any available implicit 
     * receiver.
     * @throws SLTranslationException
     */
    private SLExpression resolveImplicit(String name, SLParameters parameters) throws SLTranslationException {
        IteratorOfNamespace it = localVariablesNamespaces.iterator();
        while(it.hasNext()) {
            Namespace ns = it.next();
            ListOfNamed elements = ns.elements();
            
            IteratorOfNamed it2 = elements.iterator();
            while(it2.hasNext()) {
                ParsableVariable localVar = (ParsableVariable) it2.next();
                if(localVar.sort() instanceof ObjectSort) {              
                    Term recTerm = tb.var(localVar);
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
        
        // the class where the specification is written can be an implicit type receiver
        // (e.g. for static attributes or static methods)
        SLExpression result = resolveExplicit(createSLExpression(specInClass),
                                name,
                                parameters);
        if(result != null) {
            return result;
        }

        return null;
    }

    private SLExpression resolveIt(SLExpression receiver,
                                String name, 
                                SLParameters parameters) throws SLTranslationException {
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

    
    private SLExpression resolveExplicit(SLExpression receiver, String name, SLParameters params) throws SLTranslationException {
        
        IteratorOfSLExpressionResolver it = resolvers.iterator();
        
        while(it.hasNext()) {
            SLExpression result = it.next().resolve(receiver, name, params);
            if (result != null) {
                return result;
            }
        }
       
        return null;
    }

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
            SLParameters parameters) throws SLTranslationException {

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

    
    private String getShortName(String name) {
        return name.substring(name.lastIndexOf(".") + 1);
    }


    private boolean isFullyQualified(String name) {
        return name.indexOf(".") > -1;
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
