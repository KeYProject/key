// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

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
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContract;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import java.util.Collections;


/**
 * Uses the class <code>QueryExpand</code> in order to insert query expansions in the term that the
 * meta construct is applied on.
 * @author gladisch
 */
public class ObserverEqualityMetaConstruct extends AbstractTermTransformer {

	public static final String name = "#ObserverEquality";

	public ObserverEqualityMetaConstruct() {
		super(new Name(name), 2, Sort.FORMULA);
	}

	/**
	 * term.sub(0) is the term that possibly contains queries.
	 * term.sub(1) is expected to be true or false. True indicates that the
	 * meta construct appears in a positive context wrt. to logical negation, (e.g. in the succedent or negated in the antecedent)
	 * False implies means that the meta construct appears in a negative context. (e.g. in the antecedent or negated in the succedent)
	 */
	public Term transform(Term term, SVInstantiations svInst, Services services) {
		Term term1 = term.sub(0);
		Term term2 = term.sub(1);

		assert term1.op() instanceof IObserverFunction : "\\sameObserver must be true";
		assert term2.op() instanceof IObserverFunction : "\\sameObserver must be true";

		IObserverFunction obs1 = (IObserverFunction) term1.op();
		IObserverFunction obs2 = (IObserverFunction) term2.op();

		assert obs1 == obs2 : "\\sameObserver must be true";

        KeYJavaType kjt = obs1.isStatic() ?
                obs1.getContainerType() :
                services.getTypeConverter().getKeYJavaType(term1.sub(1));

		ImmutableSet<Contract> contracts =
				UseDependencyContractRule.getApplicableContracts(services, kjt, obs1);

		DependencyContract contract = (DependencyContract) contracts.iterator().next();

		Term result = services.getTermBuilder().and(
				buildConditionMonotonicHeap(term1.sub(0), term2.sub(0), services),
				buildConditionPrecondition(term2, contract, services),
				buildConditionSameParams(term1, term2, services),
				buildConditionDependency(term1, term2, contract, services)
		);

		return result;
	}

	private Term buildConditionDependency(Term larger, Term smaller,
										  DependencyContract contract, Services services) {
		//  forall o,f. o,f in dep@heap1 ==> o.f@heap1 == o.f@heap2

		TermBuilder tb = services.getTermBuilder();
		LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();

//		VariableSV varObj = SchemaVariableFactory.createVariableSV(
//				new Name("_ov"), services.getJavaInfo().getJavaLangObject().getSort());
//		VariableSV varFld = SchemaVariableFactory.createVariableSV(
//				new Name("_fv"), services.getTypeConverter().getHeapLDT().getFieldSort());
		LogicVariable varObj = new LogicVariable(new Name("_ov"),
				services.getJavaInfo().getJavaLangObject().getSort());
		LogicVariable varFld = new LogicVariable(new Name("_fv"),
				services.getTypeConverter().getHeapLDT().getFieldSort());

		Term ov = tb.var(varObj);
		Term fv = tb.var(varFld);

		ImmutableList<Term> params = smaller.subs().toImmutableList().take(2);

		Term mod = contract.getDep(baseHeap, false, smaller.sub(0),
				smaller.sub(1), params, Collections.emptyMap(), services);

		Term result = tb.all(varObj, tb.all(varFld,
				tb.imp(
						tb.elementOf(ov, fv, mod),
						tb.equals(
								tb.select(Sort.ANY, smaller.sub(0), ov, fv),
								tb.select(Sort.ANY, larger.sub(0), ov, fv)))));

		return result;
	}

	private Term buildConditionSameParams(Term term1, Term term2, Services services) {
		TermBuilder tb = services.getTermBuilder();
		Term result = tb.tt();

		for (int i = 2; i < term1.arity(); i++) {
			result = tb.and(result, tb.equals(term1.sub(i), term2.sub(i)));
		}

		return result;
	}

	private Term buildConditionPrecondition(Term app, DependencyContract contract, Services services) {

		LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
		ImmutableList<Term> params = app.subs().toImmutableList().take(2);

		return contract.getPre(baseHeap, app.sub(0), app.sub(1), params, Collections.emptyMap(), services);
	}

	private Term buildConditionMonotonicHeap(Term largerHeap, Term smallerHeap, Services services) {
		//  forall o, o.created@smaller ==> o.created@larger

		// VariableSV var = SchemaVariableFactory.createVariableSV(
		//		new Name("_ov"), services.getJavaInfo().getJavaLangObject().getSort());
		LogicVariable var = new LogicVariable(new Name("_ov"),
				services.getJavaInfo().getJavaLangObject().getSort());

		TermBuilder tb = services.getTermBuilder();

		Term ov = tb.var(var);

		return tb.all(var,
				tb.imp(
						tb.created(smallerHeap, ov),
						tb.created(largerHeap, ov)));
	}
}