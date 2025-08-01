/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.proof.init;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;

import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * Prepare program and location variables.
 * <p/>
 *
 * @author christoph
 *         <p/>
 */
public class StateVars {

    public final ImmutableList<JTerm> termList;

    public final ImmutableList<JTerm> paddedTermList;

    public final JTerm self;

    public final JTerm guard;

    public final ImmutableList<JTerm> localVars;

    public final JTerm result;

    public final JTerm exception;

    public final JTerm heap;

    public final JTerm mbyAtPre;


    public StateVars(JTerm self, JTerm guard, ImmutableList<JTerm> localVars, JTerm result,
            JTerm exception, JTerm heap, JTerm mbyAtPre) {
        this.self = self;
        this.guard = guard;
        this.localVars = localVars;
        this.result = result;
        this.exception = exception;
        this.heap = heap;
        this.mbyAtPre = mbyAtPre;

        ImmutableList<JTerm> terms = ImmutableSLList.nil();
        terms = appendIfNotNull(terms, heap);
        terms = appendIfNotNull(terms, self);
        terms = appendIfNotNull(terms, guard);
        terms = appendIfNotNull(terms, localVars);
        terms = appendIfNotNull(terms, result);
        terms = appendIfNotNull(terms, exception);
        terms = appendIfNotNull(terms, mbyAtPre);
        termList = terms;

        ImmutableList<JTerm> allTerms = ImmutableSLList.nil();
        allTerms = allTerms.append(heap);
        allTerms = allTerms.append(self);
        allTerms = allTerms.append(guard);
        allTerms = allTerms.append(localVars);
        allTerms = allTerms.append(result);
        allTerms = allTerms.append(exception);
        allTerms = allTerms.append(mbyAtPre);
        paddedTermList = allTerms;
    }


    public StateVars(JTerm self, ImmutableList<JTerm> localVars, JTerm result, JTerm exception,
            JTerm heap, JTerm mbyAtPre) {
        this(self, null, localVars, result, exception, heap, mbyAtPre);
    }


    private ImmutableList<JTerm> appendIfNotNull(ImmutableList<JTerm> list, JTerm t) {
        if (t != null) {
            return list.append(t);
        } else {
            return list;
        }
    }


    private ImmutableList<JTerm> appendIfNotNull(ImmutableList<JTerm> list,
            ImmutableList<JTerm> list2) {
        ImmutableList<JTerm> result = list;
        for (JTerm t : list2) {
            result = appendIfNotNull(result, t);
        }
        return result;
    }


    public StateVars(JTerm self, JTerm guard, ImmutableList<JTerm> localVars, JTerm heap) {
        this(self, guard, localVars, null, null, heap, null);
    }


    public StateVars(JTerm self, JTerm guard, ImmutableList<JTerm> localVars, JTerm result,
            JTerm exception, JTerm heap) {
        this(self, guard, localVars, result, exception, heap, null);
    }


    public StateVars(@Nullable @Nullable JTerm self, ImmutableList<JTerm> localVars, @Nullable @Nullable JTerm result, @Nullable @Nullable JTerm exception,
                     JTerm heap) {
        this(self, localVars, result, exception, heap, null);
    }


    public StateVars(JTerm self, ImmutableList<JTerm> localVars, JTerm heap) {
        this(self, localVars, null, null, heap);
    }


    public StateVars(StateVars orig, String postfix, Services services) {
        this(copyVariable(orig.self, postfix, services),
            copyVariable(orig.guard, postfix, services),
            copyVariables(orig.localVars, postfix, services),
            copyVariable(orig.result, postfix, services),
            copyVariable(orig.exception, postfix, services),
            copyHeapSymbol(orig.heap, postfix, services),
            copyFunction(orig.mbyAtPre, postfix, services));
    }


    private static ImmutableList<JTerm> copyVariables(ImmutableList<JTerm> ts, String postfix,
            Services services) {
        ImmutableList<JTerm> result = ImmutableSLList.nil();
        for (JTerm t : ts) {
            result = result.append(copyVariable(t, postfix, services));
        }
        return result;
    }


    private static JTerm copyVariable(JTerm t, String postfix, Services services) {
        if (t != null) {
            final TermBuilder tb = services.getTermBuilder();
            JTerm tWithoutLables = tb.unlabel(t);
            JTerm result =
                newVariable(tWithoutLables, tWithoutLables.toString() + postfix, services);
            return tb.label(result, t.getLabels());
        } else {
            return null;
        }
    }


    private static JTerm newVariable(JTerm t, String name, Services services) {
        if (t == null) {
            return null;
        }

        assert t.op() instanceof ProgramVariable : "Expected a program " + "variable.";

        final TermBuilder tb = services.getTermBuilder();
        String newName = tb.newName(name);
        ProgramElementName pen = new ProgramElementName(newName);
        ProgramVariable progVar = (ProgramVariable) t.op();
        LocationVariable newVar = LocationVariable.fromProgramVariable(progVar, pen);
        register(newVar, services);
        return tb.var(newVar);
    }


    private static JTerm copyHeapSymbol(JTerm t, String postfix, Services services) {
        if (t != null) {
            final TermBuilder tb = services.getTermBuilder();
            JTerm tWithoutLables = tb.unlabel(t);
            JTerm result =
                newHeapSymbol(tWithoutLables, tWithoutLables.toString() + postfix, services);
            return tb.label(result, t.getLabels());
        } else {
            return null;
        }
    }


    private static JTerm newHeapSymbol(JTerm t, String name, Services services) {
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


    private static JTerm newFunction(JTerm t, String name, Services services) {
        if (t == null) {
            return null;
        }
        final TermBuilder tb = services.getTermBuilder();
        final Function newFunc = new JFunction(new Name(name), t.sort());
        register(newFunc, services);
        return tb.func(newFunc);
    }


    private static JTerm copyFunction(JTerm t, String postfix, Services services) {
        if (t != null) {
            final TermBuilder tb = services.getTermBuilder();
            JTerm tWithoutLables = tb.unlabel(t);
            JTerm result =
                newFunction(tWithoutLables, tWithoutLables.toString() + postfix, services);
            return tb.label(result, t.getLabels());
        } else {
            return null;
        }
    }


    public static StateVars buildMethodContractPreVars(IProgramMethod pm, KeYJavaType kjt,
            Services services) {
        ImmutableArray<TermLabel> heapLabels =
            new ImmutableArray<>(ParameterlessTermLabel.ANON_HEAP_LABEL);
        return new StateVars(buildSelfVar(services, pm, kjt, ""), buildParamVars(services, "", pm),
            buildResultVar(pm, services, ""), buildExceptionVar(services, "", pm),
            buildHeapFunc("AtPre", heapLabels, services), buildMbyVar("", services));
    }


    public static StateVars buildMethodContractPostVars(StateVars preVars, IProgramMethod pm,
            KeYJavaType kjt, Services services) {
        final String postfix = "AtPost";
        // preVars.localVars: no local out variables
        return new StateVars(buildSelfVar(services, pm, kjt, postfix), preVars.localVars,
            buildResultVar(pm, services, postfix), buildExceptionVar(services, postfix, pm),
            buildHeapFunc(postfix, new ImmutableArray<>(), services), preVars.mbyAtPre);
    }


    public static StateVars buildInfFlowPreVars(StateVars origPreVars, String postfix,
            Services services) {
        return new StateVars(origPreVars, postfix, services);
    }


    public static StateVars buildInfFlowPostVars(StateVars origPreVars, StateVars origPostVars,
            StateVars preVars, String postfix, Services services) {
        // create new post vars if original pre and original post var differ;
        // else use pre var
        JTerm self = (origPreVars.self == origPostVars.self) ? preVars.self
                : copyVariable(origPostVars.self, postfix, services);
        JTerm guard = (origPreVars.guard == origPostVars.guard) ? preVars.guard
                : copyVariable(origPostVars.guard, postfix, services);
        JTerm result = (origPreVars.result == origPostVars.result) ? preVars.result
                : copyVariable(origPostVars.result, postfix, services);
        JTerm exception = (origPreVars.exception == origPostVars.exception) ? preVars.exception
                : copyVariable(origPostVars.exception, postfix, services);
        JTerm heap = (origPreVars.heap == origPostVars.heap) ? preVars.heap
                : copyHeapSymbol(origPostVars.heap, postfix, services);
        JTerm mbyAtPre = (origPreVars.mbyAtPre == origPostVars.mbyAtPre) ? preVars.mbyAtPre
                : copyVariable(origPostVars.mbyAtPre, postfix, services);

        ImmutableList<JTerm> localPostVars = ImmutableSLList.nil();
        Iterator<JTerm> origPreVarsIt = origPreVars.localVars.iterator();
        Iterator<JTerm> localPreVarsIt = preVars.localVars.iterator();
        for (JTerm origPostVar : origPostVars.localVars) {
            JTerm origPreVar = origPreVarsIt.next();
            JTerm localPreVar = localPreVarsIt.next();
            JTerm localPostVar = (origPreVar == origPostVar) ? localPreVar
                    : copyVariable(origPostVar, postfix, services);
            localPostVars = localPostVars.append(localPostVar);
        }
        return new StateVars(self, guard, localPostVars, result, exception, heap, mbyAtPre);
    }


    private static JTerm buildSelfVar(Services services, IProgramMethod pm, KeYJavaType kjt,
            String postfix) {
        if (pm.isStatic()) {
            return null;
        }
        final TermBuilder tb = services.getTermBuilder();
        JTerm selfVar = tb.var(tb.selfVar(pm, kjt, true, postfix));
        register(selfVar.op(ProgramVariable.class), services);
        return selfVar;
    }


    private static ImmutableList<JTerm> buildParamVars(Services services, String postfix,
            IProgramMethod pm) {
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<JTerm> paramVars = tb.var(tb.paramVars(postfix, pm, true));
        register(ops(paramVars, ProgramVariable.class), services);
        return paramVars;
    }


    private static JTerm buildResultVar(IProgramMethod pm, Services services, String postfix) {
        if (pm.isVoid() || pm.isConstructor()) {
            return null;
        }
        final TermBuilder tb = services.getTermBuilder();
        JTerm resultVar = tb.var(tb.resultVar("result" + postfix, pm, true));
        register(resultVar.op(ProgramVariable.class), services);
        return resultVar;
    }


    private static JTerm buildHeapFunc(String postfix, ImmutableArray<TermLabel> labels,
            Services services) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();
        if ("".equals(postfix)) {
            return tb.getBaseHeap();
        } else {
            Name heapName = new Name("heap" + postfix);
            Function heap = new JFunction(heapName, heapLDT.getHeap().sort());
            JTerm heapFunc = tb.func(heap);
            register(heap, services);
            return tb.label(heapFunc, labels);
        }
    }


    private static JTerm buildExceptionVar(Services services, String postfix, IProgramMethod pm) {
        final TermBuilder tb = services.getTermBuilder();
        JTerm excVar = tb.var(tb.excVar("exc" + postfix, pm, true));
        register(excVar.op(ProgramVariable.class), services);
        return excVar;
    }


    private static JTerm buildMbyVar(String postfix, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        String newName = tb.newName("mbyAtPre" + postfix);
        final Function mbyAtPreFunc = new JFunction(new Name(newName), intSort);
        register(mbyAtPreFunc, services);
        return tb.func(mbyAtPreFunc);
    }


    static void register(ProgramVariable pv, Services services) {
        Namespace<IProgramVariable> progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }


    static void register(ImmutableList<ProgramVariable> pvs, Services services) {
        for (ProgramVariable pv : pvs) {
            register(pv, services);
        }
    }


    static void register(Function f, Services services) {
        Namespace<Function> functionNames = services.getNamespaces().functions();
        if (f != null && functionNames.lookup(f.name()) == null) {
            assert f.sort() != JavaDLTheory.UPDATE;
            functionNames.addSafely(f);
        }
    }


    static <T> ImmutableList<T> ops(ImmutableList<JTerm> terms, Class<T> opClass)
            throws IllegalArgumentException {
        ImmutableList<T> ops = ImmutableSLList.nil();
        for (JTerm t : terms) {
            ops = ops.append(t.op(opClass));
        }
        return ops;
    }


    @Override
    public String toString() {
        return termList.toString();
    }
}
