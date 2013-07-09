/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import java.util.Iterator;


/**
 * Prepare program and location variables.
 * <p/>
 * @author christoph
 * <p/>
 */
public class StateVars {

    protected static final TermBuilder TB = TermBuilder.DF;

    public final ImmutableList<Term> termList;

    public final ImmutableList<Term> paddedTermList;

    public final Term self;

    public final Term guard;

    public final ImmutableList<Term> localVars;

    public final Term result;

    public final Term exception;

    public final Term heap;

    public final Term mbyAtPre;


    StateVars(IProgramMethod pm,
              KeYJavaType kjt,
              Services services) {
        this(pm, kjt, "", services);
    }


    public StateVars(Term self,
                     Term guard,
                     ImmutableList<Term> localVars,
                     Term result,
                     Term exception,
                     Term heap,
                     Term mbyAtPre) {
        this.self = self;
        this.guard = guard;
        this.localVars = localVars;
        this.result = result;
        this.exception = exception;
        this.heap = heap;
        this.mbyAtPre = mbyAtPre;

        ImmutableList<Term> terms =
                ImmutableSLList.<Term>nil();
        terms = appendIfNotNull(terms, heap);
        terms = appendIfNotNull(terms, self);
        terms = appendIfNotNull(terms, guard);
        terms = appendIfNotNull(terms, localVars);
        terms = appendIfNotNull(terms, result);
        terms = appendIfNotNull(terms, exception);
        terms = appendIfNotNull(terms, mbyAtPre);
        termList = terms;

        ImmutableList<Term> allTerms =
                ImmutableSLList.<Term>nil();
        allTerms = allTerms.append(heap);
        allTerms = allTerms.append(self);
        allTerms = allTerms.append(guard);
        allTerms = allTerms.append(localVars);
        allTerms = allTerms.append(result);
        allTerms = allTerms.append(exception);
        allTerms = allTerms.append(mbyAtPre);
        paddedTermList = allTerms;
    }


    public StateVars(Term self,
                     ImmutableList<Term> localVars,
                     Term result,
                     Term exception,
                     Term heap,
                     Term mbyAtPre) {
        this(self, null, localVars, result, exception, heap, mbyAtPre);
    }


    private ImmutableList<Term> appendIfNotNull(ImmutableList<Term> list,
                                                Term t) {
        if (t != null) {
            return list.append(t);
        } else {
            return list;
        }
    }


    private ImmutableList<Term> appendIfNotNull(ImmutableList<Term> list,
                                                ImmutableList<Term> list2) {
        ImmutableList<Term> result = list;
        for (Term t : list2) {
            result = appendIfNotNull(result, t);
        }
        return result;
    }


    public StateVars(Term self,
                     Term guard,
                     ImmutableList<Term> localVars,
                     Term heap) {
        this(self, guard, localVars, null, null, heap, null);
    }


    public StateVars(Term self,
                     Term guard,
                     ImmutableList<Term> localVars,
                     Term heap,
                     Term result,
                     Term exception) {
        this(self, guard, localVars, result, exception, heap, null);
    }


    public StateVars(Term self,
                     ImmutableList<Term> localVars,
                     Term heap,
                     Term result,
                     Term exception) {
        this(self, localVars, result, exception, heap, null);
    }


    public StateVars(Term self,
                     ImmutableList<Term> localVars,
                     Term heap) {
        this(self, localVars, heap, null, null);
    }


    public StateVars(StateVars orig,
                     String postfix,
                     Services services) {
        this(copyLocationVariable(orig.self, postfix, services),
             copyLocationVariable(orig.guard, postfix, services),
             copyLocationVariable(orig.localVars, postfix, services),
             copyLocationVariable(orig.result, postfix, services),
             copyLocationVariable(orig.exception, postfix, services),
             copyLocationVariable(orig.heap, postfix, services),
             newFunction(orig.mbyAtPre, postfix, services));
    }


    private static Term copyLocationVariable(Term t,
                                             String postfix,
                                             Services services) {
        if (t != null) {
            return newLocationVariable(t, t.toString() + postfix, services);
        } else {
            return null;
        }
    }


    private static Term newLocationVariable(Term t,
                                            String name,
                                            Services services) {
        if (t == null) {
            return null;
        }
        String newName = TB.newName(services, name);
        ProgramElementName pen = new ProgramElementName(newName);
        LocationVariable newVar;
        if (t.op() instanceof ProgramVariable) {
            // normal case
            ProgramVariable progVar = (ProgramVariable) t.op();
            newVar = new LocationVariable(pen, progVar.getKeYJavaType(),
                                          progVar.getContainerType(),
                                          progVar.isStatic(), progVar.isModel());
        } else if (t.op() instanceof Function) {
            // might be the case if a new heap-symbol has been introduced
            Function f = (Function) t.op();
            LocationVariable heapVar =
                    services.getTypeConverter().getHeapLDT().getHeap();
            if (f.sort() == heapVar.sort()) {
                newVar = new LocationVariable(pen, heapVar.getKeYJavaType());
            } else {
                throw new IllegalArgumentException("Expected a program " +
                                                   "variable or a function " +
                                                   "of sort Heap.");
            }
        } else {
            throw new IllegalArgumentException("Expected a program " +
                                               "variable or a function of " +
                                               "sort Heap.");
        }
        register(newVar, services);
        return TB.var(newVar);
    }


    private static ImmutableList<Term> copyLocationVariable(ImmutableList<Term> ts,
                                                            String postfix,
                                                            Services services) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (Term t : ts) {
            result = result.append(copyLocationVariable(t, postfix, services));
        }
        return result;
    }


    private static Term newFunction(Term t,
                                    String postfix,
                                    Services services) {
        if (t == null) {
            return null;
        }
        String newName = TB.newName(services, t.toString() + postfix);
        final Function newFunc =
                new Function(new Name(newName), t.sort());
        register(newFunc, services);
        return TB.func(newFunc);
    }


    StateVars(IProgramMethod pm,
              KeYJavaType kjt,
              String postfix,
              Services services) {
        this(buildSelfVar(services, pm, kjt, postfix),
             buildParamVars(services, postfix, pm),
             buildResultVar(pm, services, postfix),
             buildExceptionVar(services, postfix, pm),
             buildHeapVar(postfix, services),
             buildMbyVar(postfix, services));
    }


    public static StateVars buildMethodContractPreVars(IProgramMethod pm,
                                                       KeYJavaType kjt,
                                                       Services services) {
        return new StateVars(buildSelfVar(services, pm, kjt, ""),
                             buildParamVars(services, "", pm),
                             buildResultVar(pm, services, ""),
                             buildExceptionVar(services, "", pm),
                             buildHeapVar("AtPre", services),
                             buildMbyVar("", services));
    }


    public static StateVars buildMethodContractPostVars(StateVars preVars,
                                                        IProgramMethod pm,
                                                        KeYJavaType kjt,
                                                        Services services) {
        final String postfix = "AtPost";
        return new StateVars(buildSelfVar(services, pm, kjt, postfix),
                             preVars.localVars, // no local out variables
                             buildResultVar(pm, services, postfix),
                             buildExceptionVar(services, postfix, pm),
                             buildHeapVar(postfix, services),
                             preVars.mbyAtPre);
    }


    public static StateVars buildInfFlowPreVars(StateVars origPreVars,
                                                String postfix,
                                                Services services) {
        return new StateVars(origPreVars, postfix, services);
    }


    public static StateVars buildInfFlowPostVars(StateVars origPreVars,
                                                 StateVars origPostVars,
                                                 StateVars preVars,
                                                 String postfix,
                                                 Services services) {
        // create new post vars if original pre and original post var differ;
        // else use pre var
        Term self = (origPreVars.self == origPostVars.self) ?
                    preVars.self :
                    copyLocationVariable(origPostVars.self, postfix, services);
        Term guard = (origPreVars.guard == origPostVars.guard) ?
                     preVars.guard :
                     copyLocationVariable(origPostVars.guard, postfix, services);
        Term result = (origPreVars.result == origPostVars.result) ?
                    preVars.result :
                    copyLocationVariable(origPostVars.result, postfix, services);
        Term exception = (origPreVars.exception == origPostVars.exception) ?
                    preVars.exception :
                    copyLocationVariable(origPostVars.exception, postfix, services);
        Term heap = (origPreVars.heap == origPostVars.heap) ?
                    preVars.heap :
                    copyLocationVariable(origPostVars.heap, postfix, services);
        Term mbyAtPre = (origPreVars.mbyAtPre == origPostVars.mbyAtPre) ?
                    preVars.mbyAtPre :
                    copyLocationVariable(origPostVars.mbyAtPre, postfix, services);

        ImmutableList<Term> localPostVars = ImmutableSLList.<Term>nil();
        Iterator<Term> origPreVarsIt = origPreVars.localVars.iterator();
        Iterator<Term> localPreVarsIt = preVars.localVars.iterator();
        for (Term origPostVar : origPostVars.localVars) {
            Term origPreVar = origPreVarsIt.next();
            Term localPreVar = localPreVarsIt.next();
            Term localPostVar = (origPreVar == origPostVar) ?
                    localPreVar :
                    copyLocationVariable(origPostVar, postfix, services);
            localPostVars = localPostVars.append(localPostVar);
        }
        return new StateVars(self,
                             guard,
                             localPostVars,
                             result,
                             exception,
                             heap,
                             mbyAtPre);
    }


    private static Term buildSelfVar(Services services,
                                     IProgramMethod pm,
                                     KeYJavaType kjt,
                                     String postfix) {
        if (pm.isStatic()) {
            return null;
        }
        Term selfVar = TB.var(TB.selfVar(services, pm, kjt, true, postfix));
        register(selfVar.op(ProgramVariable.class), services);
        return selfVar;
    }


    private static ImmutableList<Term> buildParamVars(Services services,
                                                      String postfix,
                                                      IProgramMethod pm) {
        ImmutableList<Term> paramVars =
                TB.var(TB.paramVars(services, postfix, pm, true));
        register(ops(paramVars, ProgramVariable.class), services);
        return paramVars;
    }


    private static Term buildResultVar(IProgramMethod pm,
                                       Services services,
                                       String postfix) {
        if (pm.isVoid() || pm.isConstructor()) {
            return null;
        }
        Term resultVar =
                TB.var(TB.resultVar(services, "result" + postfix, pm, true));
        register(resultVar.op(ProgramVariable.class), services);
        return resultVar;
    }


    private static Term buildHeapVar(String postfix,
                                     Services services) {
        if ("".equals(postfix)) {
            return TB.getBaseHeap(services);
        } else {
            Term heapVar =
                    TB.var(TB.heapAtPreVar(services, "heap" + postfix, true));
            register(heapVar.op(LocationVariable.class), services);
            return heapVar;
        }
    }


    private static Term buildExceptionVar(Services services,
                                          String postfix,
                                          IProgramMethod pm) {
        Term excVar = TB.var(TB.excVar(services, "exc" + postfix, pm, true));
        register(excVar.op(ProgramVariable.class), services);
        return excVar;
    }


    private static Term buildMbyVar(String postfix,
                                    Services services) {
        final Sort intSort =
                services.getTypeConverter().getIntegerLDT().targetSort();
        String newName = TB.newName(services, "mbyAtPre" + postfix);
        final Function mbyAtPreFunc =
                new Function(new Name(newName), intSort);
        register(mbyAtPreFunc, services);
        return TB.func(mbyAtPreFunc);
    }


    static void register(ProgramVariable pv,
                         Services services) {
        Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }


    static void register(ImmutableList<ProgramVariable> pvs,
                         Services services) {
        for (ProgramVariable pv : pvs) {
            register(pv, services);
        }
    }


    static void register(Function f,
                         Services services) {
        Namespace functionNames = services.getNamespaces().functions();
        if (f != null && functionNames.lookup(f.name()) == null) {
            assert f.sort() != Sort.UPDATE;
            if (f.sort() == Sort.FORMULA) {
                functionNames.addSafely(f);
            } else {
                functionNames.addSafely(f);
            }
        }
    }


    static <T> ImmutableList<T> ops(ImmutableList<Term> terms,
                                    Class<T> opClass)
            throws IllegalArgumentException {
        ImmutableList<T> ops = ImmutableSLList.<T>nil();
        for (Term t : terms) {
            ops = ops.append(t.op(opClass));
        }
        return ops;
    }


    @Override
    public String toString() {
        return termList.toString();
    }
}