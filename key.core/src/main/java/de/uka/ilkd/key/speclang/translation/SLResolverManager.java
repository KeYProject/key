/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.translation;


import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * Resolves property calls of any kind. Keeps a list of resolvers doing the actual work, and a stack
 * of namespaces to deal with several levels of local variables (e.g. "self", or iterator variables
 * in forall() or select() subtrees).
 */
public abstract class SLResolverManager {

    public final SLExceptionFactory excManager;

    private ImmutableList<SLExpressionResolver> resolvers =
        ImmutableSLList.nil();
    private final KeYJavaType specInClass;
    private final ParsableVariable selfVar;
    private final boolean useLocalVarsAsImplicitReceivers;
    private final TermBuilder tb;

    private ImmutableList<Namespace<ParsableVariable>> localVariablesNamespaces =
        ImmutableSLList.nil();

    private final Map<ParsableVariable, KeYJavaType> kjts = new LinkedHashMap<>();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    protected SLResolverManager(SLExceptionFactory excManager, KeYJavaType specInClass,
            ParsableVariable selfVar, boolean useLocalVarsAsImplicitReceivers, TermBuilder tb) {
        // assert excManager != null;
        this.excManager = excManager;
        this.specInClass = specInClass;
        this.selfVar = selfVar;
        this.useLocalVarsAsImplicitReceivers = useLocalVarsAsImplicitReceivers;
        this.tb = tb;
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    protected void addResolver(SLExpressionResolver resolver) {
        assert resolver != null;
        resolvers = resolvers.append(resolver);
    }


    private String getShortName(String name) {
        return name.substring(name.lastIndexOf('.') + 1);
    }


    private boolean isFullyQualified(String name) {
        return name.contains(".");
    }


    /**
     * Tries to resolve a name as a local variable.
     */
    private SLExpression resolveLocal(String name) {
        Name n = new Name(name);
        for (Namespace<?> ns : localVariablesNamespaces) {
            ParsableVariable localVar = (ParsableVariable) ns.lookup(n);
            if (localVar != null) {
                Term varTerm = tb.var(localVar);
                return new SLExpression(varTerm, kjts.get(localVar));
            }
        }

        return null;
    }


    /**
     * Tries to resolve a name as a property call on any available implicit receiver.
     */
    private SLExpression resolveImplicit(String name, SLParameters parameters)
            throws SLTranslationException {
        if (useLocalVarsAsImplicitReceivers) {
            for (Namespace<?> ns : localVariablesNamespaces) {
                for (Named n : ns.elements()) {
                    ParsableVariable localVar = (ParsableVariable) n;
                    SLExpression receiver = new SLExpression(tb.var(localVar), kjts.get(localVar));

                    SLExpression result = resolveExplicit(receiver, name, parameters);
                    if (result != null) {
                        return result;
                    }
                }
            }
        } else if (selfVar != null) {
            SLExpression receiver = new SLExpression(tb.var(selfVar), specInClass);
            SLExpression result = resolveExplicit(receiver, name, parameters);
            if (result != null) {
                return result;
            }
        }

        // the class where the specification is written can be an implicit type receiver
        // (e.g. for static attributes or static methods)
        if (specInClass != null) {
            SLExpression receiver = new SLExpression(specInClass);
            return resolveExplicit(receiver, name, parameters);
        }

        return null;
    }


    /**
     * Tries to resolve a name as a property call on an explicitly given receiver, by calling the
     * registered resolvers.
     */
    private SLExpression resolveExplicit(SLExpression receiver, String name, SLParameters params)
            throws SLTranslationException {
        for (SLExpressionResolver resolver : resolvers) {
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
    private SLExpression resolveIt(SLExpression receiver, String name, SLParameters parameters)
            throws SLTranslationException {
        SLExpression result;

        if (receiver != null) {
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


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Resolves arbitrary property calls.
     *
     * @param receiver the specified explicit receiver, or null
     * @param name name of the property
     * @param parameters actual parameters of the property call, or null
     * @return corresponding term, type or collection if successful, null otherwise
     */
    public SLExpression resolve(SLExpression receiver, String name, SLParameters parameters)
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
        var ns = new Namespace<ParsableVariable>();
        localVariablesNamespaces = localVariablesNamespaces.prepend(ns);
    }


    /**
     * Puts a local variable into the topmost namespace on the stack
     */
    public void putIntoTopLocalVariablesNamespace(ParsableVariable pv, KeYJavaType kjt) {
        localVariablesNamespaces.head().addSafely(pv);
        kjts.put(pv, kjt);
    }


    /**
     * Puts a local variable into the topmost namespace on the stack
     */
    public void putIntoTopLocalVariablesNamespace(ProgramVariable pv) {
        putIntoTopLocalVariablesNamespace(pv, pv.getKeYJavaType());
    }


    /**
     * Puts a list of local variables into the topmost namespace on the stack.
     */
    public void putIntoTopLocalVariablesNamespace(ImmutableList<LogicVariable> pvs,
            KeYJavaType kjt) {
        for (LogicVariable pv : pvs) {
            putIntoTopLocalVariablesNamespace(pv, kjt);
        }
    }


    /**
     * Puts a list of local variables into the topmost namespace on the stack.
     */
    public void putIntoTopLocalVariablesNamespace(ImmutableList<? extends ProgramVariable> pvs) {
        for (ProgramVariable pv : pvs) {
            putIntoTopLocalVariablesNamespace(pv, pv.getKeYJavaType());
        }
    }


    /**
     * Throws away the topmost namespace on the stack.
     */
    public void popLocalVariablesNamespace() {
        localVariablesNamespaces = localVariablesNamespaces.tail();
    }


    /**
     * Returns a specification-language based visibility level for the passed member that should
     * take precedence over Java's ordinary visibility, or null.
     */
    public VisibilityModifier getSpecVisibility(MemberDeclaration md) {
        return null;
    }
}
