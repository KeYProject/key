/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
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

    public final ImmutableList<Term> termList;

    public final ImmutableList<Term> paddedTermList;

    public final Term self;

    public final Term guard;

    public final ImmutableList<Term> localVars;

    public final Term result;

    public final Term exception;

    public final Term heap;

    public final Term mbyAtPre;


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
                     Term result,
                     Term exception,
                     Term heap) {
        this(self, guard, localVars, result, exception, heap, null);
    }


    public StateVars(Term self,
                     ImmutableList<Term> localVars,
                     Term result,
                     Term exception,
                     Term heap) {
        this(self, localVars, result, exception, heap, null);
    }


    public StateVars(Term self,
                     ImmutableList<Term> localVars,
                     Term heap) {
        this(self, localVars, null, null, heap);
    }


    public StateVars(StateVars orig,
                     String postfix,
                     Services services) {
        this(copyVariable(orig.self, postfix, services),
             copyVariable(orig.guard, postfix, services),
             copyVariables(orig.localVars, postfix, services),
             copyVariable(orig.result, postfix, services),
             copyVariable(orig.exception, postfix, services),
             copyHeapSymbol(orig.heap, postfix, services),
             copyFunction(orig.mbyAtPre, postfix, services));
    }


    private static ImmutableList<Term> copyVariables(ImmutableList<Term> ts,
                                                     String postfix,
                                                     Services services) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (Term t : ts) {
            result = result.append(copyVariable(t, postfix, services));
        }
        return result;
    }


    private static Term copyVariable(Term t,
                                     String postfix,
                                     Services services) {
        if (t != null) {
            final TermBuilder tb = services.getTermBuilder();
            Term tWithoutLables = tb.unlabel(t);
            Term result =
                   newVariable(tWithoutLables, tWithoutLables.toString() + postfix, services);
            return tb.label(result, t.getLabels());
        } else {
            return null;
        }
    }


    private static Term newVariable(Term t,
                                    String name,
                                    Services services) {
        if (t == null) {
            return null;
        }

        assert t.op() instanceof ProgramVariable : "Expected a program " +
                                                   "variable.";

        final TermBuilder tb = services.getTermBuilder();
        String newName = tb.newName(name);
        ProgramElementName pen = new ProgramElementName(newName);
        ProgramVariable progVar = (ProgramVariable) t.op();
        LocationVariable newVar = new LocationVariable(pen, progVar.getKeYJavaType(),
                                                       progVar.getContainerType(),
                                                       progVar.isStatic(), progVar.isModel());
        register(newVar, services);
        return tb.var(newVar);
    }


    private static Term copyHeapSymbol(Term t,
                                       String postfix,
                                       Services services) {
        if (t != null) {
            final TermBuilder tb = services.getTermBuilder();
            Term tWithoutLables = tb.unlabel(t);
            Term result =
                   newHeapSymbol(tWithoutLables, tWithoutLables.toString() + postfix, services);
            return tb.label(result, t.getLabels());
        } else {
            return null;
        }
    }


    private static Term newHeapSymbol(Term t,
                                      String name,
                                      Services services) {
        if (t == null) {
            return null;
        }
        if (!(t.op() instanceof Function)) {
            // Sometimes the heap term operator is a location variable (for
            // instance if it is the base heap). Create a location variable
            // in this case.
            return newVariable(t, name, services);
        } else {
            // Otherwise (this is the normal case), the heap term operator is
            // a function (for instance if it is a anon heap). Create a function
            // in this case.
            return newFunction(t, name, services);
        }
    }


    private static Term newFunction(Term t,
                                    String name,
                                    Services services) {
        if (t == null) {
            return null;
        }
        final TermBuilder tb = services.getTermBuilder();
        final Function newFunc = new Function(new Name(name), t.sort());
        register(newFunc, services);
        return tb.func(newFunc);
    }


    private static Term copyFunction(Term t,
                                     String postfix,
                                     Services services) {
        if (t != null) {
            final TermBuilder tb = services.getTermBuilder();
            Term tWithoutLables = tb.unlabel(t);
            Term result =
                   newFunction(tWithoutLables, tWithoutLables.toString() + postfix, services);
            return tb.label(result, t.getLabels());
        } else {
            return null;
        }
    }


    public static StateVars buildMethodContractPreVars(IProgramMethod pm,
                                                       KeYJavaType kjt,
                                                       Services services) {
        ImmutableArray<TermLabel> heapLabels =
                new ImmutableArray<TermLabel>(ParameterlessTermLabel.ANON_HEAP_LABEL);
        return new StateVars(buildSelfVar(services, pm, kjt, ""),
                             buildParamVars(services, "", pm),
                             buildResultVar(pm, services, ""),
                             buildExceptionVar(services, "", pm),
                             buildHeapFunc("AtPre", heapLabels, services),
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
                             buildHeapFunc(postfix,
                                           new ImmutableArray<TermLabel>(),
                                           services),
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
                    copyVariable(origPostVars.self, postfix, services);
        Term guard = (origPreVars.guard == origPostVars.guard) ?
                     preVars.guard :
                     copyVariable(origPostVars.guard, postfix, services);
        Term result = (origPreVars.result == origPostVars.result) ?
                    preVars.result :
                    copyVariable(origPostVars.result, postfix, services);
        Term exception = (origPreVars.exception == origPostVars.exception) ?
                    preVars.exception :
                    copyVariable(origPostVars.exception, postfix, services);
        Term heap = (origPreVars.heap == origPostVars.heap) ?
                    preVars.heap :
                    copyHeapSymbol(origPostVars.heap, postfix, services);
        Term mbyAtPre = (origPreVars.mbyAtPre == origPostVars.mbyAtPre) ?
                    preVars.mbyAtPre :
                    copyVariable(origPostVars.mbyAtPre, postfix, services);

        ImmutableList<Term> localPostVars = ImmutableSLList.<Term>nil();
        Iterator<Term> origPreVarsIt = origPreVars.localVars.iterator();
        Iterator<Term> localPreVarsIt = preVars.localVars.iterator();
        for (Term origPostVar : origPostVars.localVars) {
            Term origPreVar = origPreVarsIt.next();
            Term localPreVar = localPreVarsIt.next();
            Term localPostVar = (origPreVar == origPostVar) ?
                    localPreVar :
                    copyVariable(origPostVar, postfix, services);
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
        final TermBuilder tb = services.getTermBuilder();
        Term selfVar = tb.var(tb.selfVar(pm, kjt, true, postfix));
        register(selfVar.op(ProgramVariable.class), services);
        return selfVar;
    }


    private static ImmutableList<Term> buildParamVars(Services services,
                                                      String postfix,
                                                      IProgramMethod pm) {
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<Term> paramVars =
                tb.var(tb.paramVars(postfix, pm, true));
        register(ops(paramVars, ProgramVariable.class), services);
        return paramVars;
    }


    private static Term buildResultVar(IProgramMethod pm,
                                       Services services,
                                       String postfix) {
        if (pm.isVoid() || pm.isConstructor()) {
            return null;
        }
        final TermBuilder tb = services.getTermBuilder();
        Term resultVar =
                tb.var(tb.resultVar("result" + postfix, pm, true));
        register(resultVar.op(ProgramVariable.class), services);
        return resultVar;
    }


    private static Term buildHeapFunc(String postfix,
                                      ImmutableArray<TermLabel> labels,
                                      Services services) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();
        if ("".equals(postfix)) {
            return tb.getBaseHeap();
        } else {
            Name heapName = new Name("heap" + postfix);
            Function heap =
                     new Function(heapName, heapLDT.getHeap().sort());
            Term heapFunc = tb.func(heap);
            register(heap, services);
            return tb.label(heapFunc, labels);
        }
    }


    private static Term buildExceptionVar(Services services,
                                          String postfix,
                                          IProgramMethod pm) {
        final TermBuilder tb = services.getTermBuilder();
        Term excVar = tb.var(tb.excVar("exc" + postfix, pm, true));
        register(excVar.op(ProgramVariable.class), services);
        return excVar;
    }


    private static Term buildMbyVar(String postfix,
                                    Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Sort intSort =
                services.getTypeConverter().getIntegerLDT().targetSort();
        String newName = tb.newName("mbyAtPre" + postfix);
        final Function mbyAtPreFunc =
                new Function(new Name(newName), intSort);
        register(mbyAtPreFunc, services);
        return tb.func(mbyAtPreFunc);
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