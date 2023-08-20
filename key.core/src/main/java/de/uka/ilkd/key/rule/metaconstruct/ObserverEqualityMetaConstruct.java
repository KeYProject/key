/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Collections;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.conditions.SameObserverCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContract;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;


/**
 * This meta contruct allows one to prove equality (equivalence) of two observer terms if they
 * belong to the same observer function symbol.
 * <p>
 * It takes two arguments of any sort and the result is a formula.
 * <p>
 * This construct is asymmetric. The second argument is the call with the base heap, i.e., the one
 * with fewer created objects. The first argument is the one with the larger heap, i.e., after
 * modification and with potentially more created objects.
 * <p>
 * The construct implements the condition (9.10) in Sect. 9.4.4 in the new KeY book.
 * <p>
 * It is probably less efficient than {@link UseDependencyContractRule}, however it is more
 * generally applicable. It mitigates the problem, that in interactive proving the above builtin
 * rule is often not available if desired.
 *
 * <h3>Limitation</h3>
 *
 * Currently it works only for observable functions that depend on a single heap. If applied to more
 * than one heap than the secondary heaps must be equal and are not treated using dependency
 * contracts.
 *
 * @author Mattias Ulbrich 2019
 * @see UseDependencyContractRule
 * @see SameObserverCondition
 */
public class ObserverEqualityMetaConstruct extends AbstractTermTransformer {

    /**
     * The unique identifier name.
     */
    public static final String NAME = "#ObserverEquality";

    /**
     * This constructor is probably only called from {@link AbstractTermTransformer}.
     */
    public ObserverEqualityMetaConstruct() {
        super(new Name(NAME), 2, Sort.FORMULA);
    }

    /**
     * Given two terms termExt and termBase, produce a formula which implies equality of the two
     * terms.
     *
     * <h3>Precondition</h3> The two terms must be belong to the same function symbol. That symbol
     * must be an observer and must possess a dependency contract.
     * <p>
     * It is easy to write a taclet that violates this. The method should therefore been written
     * defensively. Since the method must not throw declared exceptions,
     * {@link IllegalArgumentException}s are used.
     *
     * <h3>Postcondition</h3> It returns a formula that is a conjunction. It implies the equality of
     * termExt and termBase.
     *
     * @param term A term of the type {@code #ObserverEquality(t1, t2)}, not null.
     * @param svInst instantiations of schema variables, not used
     * @param services non-null {@link Services}
     * @return a non-null Term of sort FORMULA
     * @throws IllegalArgumentException if the term argument is not as expected
     */
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        Term termExt = term.sub(0);
        Term termBase = term.sub(1);

        if (!(termExt.op() instanceof IObserverFunction)
                || !(termBase.op() instanceof IObserverFunction)) {
            throw new IllegalArgumentException("\\sameObserver must be true for " + NAME);
        }
        IObserverFunction obs1 = (IObserverFunction) termExt.op();
        IObserverFunction obs2 = (IObserverFunction) termBase.op();

        if (obs1 != obs2) {
            throw new IllegalArgumentException("\\sameObserver must be true");
        }

        KeYJavaType kjt = obs1.isStatic() ? obs1.getContainerType()
                : services.getTypeConverter().getKeYJavaType(termExt.sub(1));

        ImmutableSet<Contract> contracts =
            UseDependencyContractRule.getApplicableContracts(services, kjt, obs1);

        DependencyContract contract = (DependencyContract) contracts.iterator().next();

        Term result = services.getTermBuilder().and(
            buildConditionMonotonicHeap(termExt.sub(0), termBase.sub(0), services),
            buildConditionPrecondition(termBase, contract, services),
            buildConditionSameParams(contract, termExt, termBase, services),
            buildConditionDependency(termExt, termBase, contract, services));

        return result;
    }

    /*
     * For f(h, a1, ..., an) and f(h', a1', ..., an') build the term forall o,f. o,f in dep@h' ==>
     * o.f@h' == o.f@h
     */
    private Term buildConditionDependency(Term larger, Term smaller, DependencyContract contract,
            Services services) {


        TermBuilder tb = services.getTermBuilder();
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();

        LogicVariable varObj = new LogicVariable(new Name("_ov"),
            services.getJavaInfo().getJavaLangObject().getSort());
        LogicVariable varFld = new LogicVariable(new Name("_fv"),
            services.getTypeConverter().getHeapLDT().getFieldSort());

        Term ov = tb.var(varObj);
        Term fv = tb.var(varFld);

        // static methods do not a self var ==> one argument less to ignore (#1672)
        int paramOffset = contract.hasSelfVar() ? 2 : 1;
        ImmutableList<Term> params = smaller.subs().toImmutableList().take(paramOffset);

        Term mod = contract.getDep(baseHeap, false, smaller.sub(0), smaller.sub(1), params,
            Collections.emptyMap(), services);

        Term result = tb.all(varObj,
            tb.all(varFld,
                tb.imp(tb.elementOf(ov, fv, mod),
                    tb.equals(tb.select(Sort.ANY, smaller.sub(0), ov, fv),
                        tb.select(Sort.ANY, larger.sub(0), ov, fv)))));

        return result;
    }

    /*
     * For f(h, a1, ..., an) and f(h', a1', ..., an') build a1=a1' /\ ... /\ an=an'
     */
    private Term buildConditionSameParams(DependencyContract contract, Term term1, Term term2,
            Services services) {
        TermBuilder tb = services.getTermBuilder();
        Term result = tb.tt();

        // static methods do not a self var ==> one argument less to ignore (#1672)
        int paramOffset = contract.hasSelfVar() ? 2 : 1;

        for (int i = paramOffset; i < term1.arity(); i++) {
            result = tb.and(result, tb.equals(term1.sub(i), term2.sub(i)));
        }

        return result;
    }

    /*
     * For f(h, a1, ..., an) and f(h', a1', ..., an') build depContract_f_pre(h, a1, ..., an) by
     * instantiating that part of the contract.
     */
    private Term buildConditionPrecondition(Term app, DependencyContract contract,
            Services services) {

        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        // static methods do not a self var ==> one argument less to ignore (#1672)
        int paramOffset = contract.hasSelfVar() ? 2 : 1;
        ImmutableList<Term> params = app.subs().toImmutableList().take(paramOffset);

        return contract.getPre(baseHeap, app.sub(0), app.sub(1), params, Collections.emptyMap(),
            services);
    }

    /*
     * For f(h, a1, ..., an) and f(h', a1', ..., an') build forall o, o.created@h' ==> o.created@h
     */
    private Term buildConditionMonotonicHeap(Term largerHeap, Term smallerHeap, Services services) {

        LogicVariable var = new LogicVariable(new Name("_ov"),
            services.getJavaInfo().getJavaLangObject().getSort());

        TermBuilder tb = services.getTermBuilder();

        Term ov = tb.var(var);

        return tb.all(var, tb.imp(tb.created(smallerHeap, ov), tb.created(largerHeap, ov)));
    }
}
