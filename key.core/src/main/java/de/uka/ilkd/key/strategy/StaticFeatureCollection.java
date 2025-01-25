/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.rulefilter.SetRuleFilter;
import de.uka.ilkd.key.rule.BlockContractExternalRule;
import de.uka.ilkd.key.rule.BlockContractInternalRule;
import de.uka.ilkd.key.rule.LoopApplyHeadRule;
import de.uka.ilkd.key.rule.LoopContractExternalRule;
import de.uka.ilkd.key.rule.LoopContractInternalRule;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.QueryExpand;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.strategy.feature.AtomsSmallerThanFeature;
import de.uka.ilkd.key.strategy.feature.ComprehendedSumFeature;
import de.uka.ilkd.key.strategy.feature.ConditionalFeature;
import de.uka.ilkd.key.strategy.feature.ConstFeature;
import de.uka.ilkd.key.strategy.feature.ImplicitCastNecessary;
import de.uka.ilkd.key.strategy.feature.InstantiatedSVFeature;
import de.uka.ilkd.key.strategy.feature.MergeRuleFeature;
import de.uka.ilkd.key.strategy.feature.MonomialsSmallerThanFeature;
import de.uka.ilkd.key.strategy.feature.SeqContainsExecutableCodeFeature;
import de.uka.ilkd.key.strategy.feature.ShannonFeature;
import de.uka.ilkd.key.strategy.feature.TermSmallerThanFeature;
import de.uka.ilkd.key.strategy.feature.TriggerVarInstantiatedFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.LiteralsSmallerThanFeature;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termfeature.EqTermFeature;
import de.uka.ilkd.key.strategy.termgenerator.SequentFormulasGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SubtermGenerator;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.CompareCostsFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.LetFeature;
import org.key_project.prover.strategy.costbased.feature.SortComparisonFeature;
import org.key_project.prover.strategy.costbased.feature.SumFeature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termfeature.*;
import org.key_project.prover.strategy.costbased.termfeature.ApplyTFFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermPredicateTermFeature;

/**
 * Collection of strategy features that can be accessed statically. This class is essentially a
 * collection of constructors for various features.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class StaticFeatureCollection {

    protected static Feature<Goal> loopInvFeature(Feature<Goal> costStdInv) {
        // NOTE (DS, 2019-04-10): This feature also deactivates the built-in loop
        // scope invariant rule (always!) since we use the taclets now.
        final SetRuleFilter filterLoopInv = new SetRuleFilter();
        filterLoopInv.addRuleToSet(WhileInvariantRule.INSTANCE);
        final SetRuleFilter filterLoopScopeInv = new SetRuleFilter();
        filterLoopScopeInv.addRuleToSet(LoopScopeInvariantRule.INSTANCE);

        return ConditionalFeature.createConditional(filterLoopInv, costStdInv,
            ConditionalFeature.createConditional(filterLoopScopeInv, inftyConst()));
    }

    /**
     * @param cost The specified cost.
     * @return a feature for {@link BlockContractInternalRule} with the specified cost.
     */
    protected static Feature<Goal> blockContractInternalFeature(Feature<Goal> cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(BlockContractInternalRule.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);
    }

    /**
     * @param cost The specified cost.
     * @return a feature for {@link BlockContractExternalRule} with the specified cost.
     */
    protected static Feature<Goal> blockContractExternalFeature(Feature<Goal> cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(BlockContractExternalRule.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);
    }

    /**
     * @param cost The specified cost.
     * @return a feature for {@link LoopContractInternalRule} with the specified cost.
     */
    protected static Feature<Goal> loopContractInternalFeature(Feature<Goal> cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(LoopContractInternalRule.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);
    }

    /**
     * @param cost The specified cost.
     * @return a feature for {@link LoopContractExternalRule} with the specified cost.
     */
    protected static Feature<Goal> loopContractExternalFeature(Feature<Goal> cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(LoopContractExternalRule.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);
    }

    /**
     * @param cost The specified cost.
     * @return a feature for {@link LoopApplyHeadRule} with the specified cost.
     */
    protected static Feature<Goal> loopContractApplyHead(Feature<Goal> cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(LoopApplyHeadRule.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);
    }

    protected static Feature<Goal> methodSpecFeature(Feature<Goal> cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(UseOperationContractRule.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);
    }

    protected static Feature<Goal> querySpecFeature(Feature<Goal> cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(QueryExpand.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);
    }

    protected static Feature<Goal> mergeRuleFeature(Feature<Goal> cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(MergeRule.INSTANCE);
        return ConditionalFeature.createConditional(filter,
            SumFeature.createSum(cost, MergeRuleFeature.INSTANCE));
    }

    protected static Feature<Goal> sequentContainsNoPrograms() {
        return not(SeqContainsExecutableCodeFeature.PROGRAMS);
    }

    protected static Feature<Goal> countOccurrences(ProjectionToTerm<Goal> cutFormula) {
        final TermBuffer sf = new TermBuffer();
        final TermBuffer sub = new TermBuffer();

        return sum(sf, SequentFormulasGenerator.sequent(),
            sum(sub, SubtermGenerator.leftTraverse(sf, any()),
                // instead of any a condition which stops traversal when
                // depth(cutF) > depth(sub) would be better
                ifZero(applyTF(cutFormula, eq(sub)), longConst(1), longConst(0))));
    }

    protected static Feature<Goal> termSmallerThan(String smaller, String bigger) {
        return TermSmallerThanFeature.create(instOf(smaller), instOf(bigger));
    }

    protected static Feature<Goal> monSmallerThan(String smaller, String bigger,
            IntegerLDT numbers) {
        return MonomialsSmallerThanFeature.create(instOf(smaller), instOf(bigger), numbers);
    }

    protected static Feature<Goal> atomSmallerThan(String smaller, String bigger,
            IntegerLDT numbers) {
        return AtomsSmallerThanFeature.create(instOf(smaller), instOf(bigger), numbers);
    }

    protected static Feature<Goal> literalsSmallerThan(String smaller, String bigger,
            IntegerLDT numbers) {
        return LiteralsSmallerThanFeature.create(instOf(smaller), instOf(bigger), numbers);
    }

    protected static Feature<Goal> longConst(long a) {
        return ConstFeature.createConst(cost(a));
    }

    protected static Feature<Goal> inftyConst() {
        return ConstFeature.createConst(infty());
    }

    protected static TermFeature any() {
        return longTermConst(0);
    }

    protected static TermFeature longTermConst(long a) {
        return ConstTermFeature.createConst(cost(a));
    }

    protected static TermFeature inftyTermConst() {
        return ConstTermFeature.createConst(infty());
    }

    protected static Feature<Goal> add(Feature<Goal> a, Feature<Goal> b) {
        return SumFeature.createSum(a, b);
    }

    protected static Feature<Goal> add(Feature<Goal> a, Feature<Goal> b, Feature<Goal> c) {
        return SumFeature.createSum(a, b, c);
    }

    @SafeVarargs
    protected static Feature<Goal> add(Feature<Goal>... features) {
        return SumFeature.createSum(features);
    }

    protected static TermFeature add(TermFeature a, TermFeature b) {
        return BinarySumTermFeature.createSum(a, b);
    }

    protected static TermFeature add(TermFeature a, TermFeature b, TermFeature c) {
        // could be done more efficiently
        return add(a, add(b, c));
    }

    protected static TermFeature or(TermFeature a, TermFeature b) {
        return ifZero(a, longTermConst(0), b);
    }

    protected static TermFeature or(TermFeature a, TermFeature b, TermFeature c) {
        return or(a, or(b, c));
    }

    protected static TermFeature or(TermFeature... features) {
        TermFeature orFeature = inftyTermConst();
        for (var f : features) {
            orFeature = or(orFeature, f);
        }
        return orFeature;
    }

    protected static Feature<Goal> or(Feature<Goal> a, Feature<Goal> b) {
        return ifZero(a, longConst(0), b);
    }

    protected static Feature<Goal> or(Feature<Goal> a, Feature<Goal> b, Feature<Goal> c) {
        return or(a, or(b, c));
    }

    @SafeVarargs
    protected static Feature<Goal> or(Feature<Goal>... features) {
        Feature<Goal> orFeature = inftyConst();
        for (Feature<Goal> f : features) {
            orFeature = or(orFeature, f);
        }
        return orFeature;
    }

    protected static Feature<Goal> ifZero(Feature<Goal> cond, Feature<Goal> thenFeature) {
        return ShannonFeature.createConditionalBinary(cond, thenFeature);
    }

    protected static Feature<Goal> ifZero(Feature<Goal> cond, Feature<Goal> thenFeature,
            Feature<Goal> elseFeature) {
        return ShannonFeature.createConditionalBinary(cond, thenFeature, elseFeature);
    }

    protected static TermFeature ifZero(TermFeature cond, TermFeature thenFeature) {
        return ShannonTermFeature.createConditionalBinary(cond, thenFeature);
    }

    protected static TermFeature ifZero(TermFeature cond, TermFeature thenFeature,
            TermFeature elseFeature) {
        return ShannonTermFeature.createConditionalBinary(cond, thenFeature, elseFeature);
    }

    protected static Feature<Goal> not(Feature<Goal> f) {
        return ifZero(f, inftyConst(), longConst(0));
    }

    protected static TermFeature not(TermFeature f) {
        return ifZero(f, ConstTermFeature.createConst(TopRuleAppCost.INSTANCE), longTermConst(0));
    }

    protected static Feature<Goal> eq(Feature<Goal> a, Feature<Goal> b) {
        return CompareCostsFeature.eq(a, b);
    }

    protected static Feature<Goal> less(Feature<Goal> a, Feature<Goal> b) {
        return CompareCostsFeature.less(a, b);
    }

    protected static Feature<Goal> leq(Feature<Goal> a, Feature<Goal> b) {
        return CompareCostsFeature.leq(a, b);
    }

    protected static RuleAppCost cost(long p) {
        return NumberRuleAppCost.create(p);
    }

    private static RuleAppCost infty() {
        return TopRuleAppCost.INSTANCE;
    }

    /**
     * Create a projection of taclet applications to the instantiation of the trigger variable of a
     * taclet. If the trigger variable is not instantiated for a particular taclet app, an error
     * will be raised
     *
     * @return projection of taclet applications
     */
    protected static ProjectionToTerm<Goal> instOfTriggerVariable() {
        return new TriggerVariableInstantiationProjection();
    }

    /**
     * Create a projection of taclet applications to the instantiation of the schema variables
     * <code>schemaVar</code>. If <code>schemaVar</code> is not instantiated for a particular taclet
     * app, an error will be raised
     *
     * @param schemaVar schema variable
     * @return projection of taclet applications
     */
    protected static ProjectionToTerm<Goal> instOf(String schemaVar) {
        return SVInstantiationProjection.create(new Name(schemaVar), true);
    }

    /**
     * Create a projection of taclet applications to the instantiation of the schema variables
     * <code>schemaVar</code>. The projection will be partial and undefined for those taclet
     * applications that do not instantiate <code>schemaVar</code>
     *
     * @param schemaVar schema variable
     * @return projection of taclet applications
     */
    protected static ProjectionToTerm<Goal> instOfNonStrict(String schemaVar) {
        return SVInstantiationProjection.create(new Name(schemaVar), false);
    }

    protected static ProjectionToTerm<Goal> subAt(ProjectionToTerm<Goal> t, PosInTerm pit) {
        return SubtermProjection.create(t, pit);
    }

    protected static ProjectionToTerm<Goal> sub(ProjectionToTerm<Goal> t, int index) {
        return SubtermProjection.create(t, PosInTerm.getTopLevel().down(index));
    }

    protected static ProjectionToTerm<Goal> opTerm(de.uka.ilkd.key.logic.op.Operator op,
            ProjectionToTerm<Goal>[] subTerms) {
        return TermConstructionProjection.create(op, subTerms);
    }

    protected static ProjectionToTerm<Goal> opTerm(de.uka.ilkd.key.logic.op.Operator op,
            ProjectionToTerm<Goal> subTerm) {
        // noinspection unchecked
        return opTerm(op, new ProjectionToTerm[] { subTerm });
    }

    protected static ProjectionToTerm<Goal> opTerm(de.uka.ilkd.key.logic.op.Operator op,
            ProjectionToTerm<Goal> subTerm0,
            ProjectionToTerm<Goal> subTerm1) {
        // noinspection unchecked
        return opTerm(op, new ProjectionToTerm[] { subTerm0, subTerm1 });
    }

    protected static Feature<Goal> isInstantiated(String schemaVar) {
        return InstantiatedSVFeature.create(new Name(schemaVar));
    }

    protected static Feature<Goal> isTriggerVariableInstantiated() {
        return TriggerVarInstantiatedFeature.INSTANCE;
    }

    protected static TermFeature op(org.key_project.logic.op.Operator op) {
        return OperatorTF.create(op);
    }

    protected static TermFeature rec(TermFeature cond, TermFeature summand) {
        return RecSubTermFeature.create(cond, summand);
    }

    protected static TermFeature sub(TermFeature sub0) {
        return SubTermFeature.create(new TermFeature[] { sub0 });
    }

    protected static TermFeature sub(TermFeature sub0, TermFeature sub1) {
        return SubTermFeature.create(new TermFeature[] { sub0, sub1 });
    }

    protected static TermFeature opSub(Operator op, TermFeature sub0) {
        return add(op(op), sub(sub0));
    }

    protected static TermFeature opSub(Operator op, TermFeature sub0, TermFeature sub1) {
        return add(op(op), sub(sub0, sub1));
    }

    protected static TermFeature eq(TermBuffer t) {
        return EqTermFeature.create(t);
    }

    protected static Feature<Goal> eq(ProjectionToTerm<Goal> t1, ProjectionToTerm<Goal> t2) {
        final TermBuffer buf = new TermBuffer();
        return let(buf, t1, applyTF(t2, eq(buf)));
    }


    protected static Feature<Goal> directlyBelowSymbolAtIndex(Operator symbol, int index) {
        return directlyBelowSymbolAtIndex(op(symbol), index);
    }

    protected static Feature<Goal> directlyBelowSymbolAtIndex(TermFeature symbolTF, int index) {
        final var oneUp = FocusProjection.create(1);
        if (index == -1) {
            return applyTF(oneUp, symbolTF);
        }
        return ifZero(applyTF(oneUp, symbolTF), eq(sub(oneUp, index), FocusProjection.INSTANCE),
            inftyConst());
    }

    protected static Feature<Goal> contains(ProjectionToTerm<Goal> bigTerm,
            ProjectionToTerm<Goal> searchedTerm) {
        final TermBuffer buf = new TermBuffer();
        return let(buf, searchedTerm, applyTF(bigTerm, not(rec(any(), not(eq(buf))))));
    }

    protected static Feature<Goal> println(ProjectionToTerm<Goal> t) {
        return applyTF(t, PrintTermFeature.INSTANCE);
    }

    protected static TermFeature extendsTrans(Sort s) {
        return SortExtendsTransTermFeature.create(s);
    }

    /**
     * Invoke the term feature <code>tf</code> on the term that instantiation of
     * <code>schemaVar</code>. This is the strict/safe version that raises an error of
     * <code>schemaVar</code> is not instantiated for a particular taclet app
     *
     * @param schemaVar schema variable
     * @param tf term feature
     * @return feature
     */
    protected static Feature<Goal> applyTF(String schemaVar, TermFeature tf) {
        return applyTF(instOf(schemaVar), tf);
    }

    /**
     * Invoke the term feature <code>tf</code> on the term that instantiation of
     * <code>schemaVar</code>. This is the non-strict/unsafe version that simply returns zero if
     * <code>schemaVar</code> is not instantiated for a particular taclet app
     *
     * @param schemaVar schema variable
     * @param tf term feature
     * @return feature
     */
    protected static Feature<Goal> applyTFNonStrict(String schemaVar, TermFeature tf) {
        return applyTFNonStrict(instOfNonStrict(schemaVar), tf);
    }

    /**
     * Evaluate the term feature <code>tf</code> for the term described by the projection
     * <code>term</code>. If <code>term</code> is undefined for a particular rule app, an exception
     * is raised
     *
     * @param term term describing the projection
     * @param tf term feature
     * @return feature
     */
    protected static Feature<Goal> applyTF(ProjectionToTerm<Goal> term, TermFeature tf) {
        return ApplyTFFeature.create(term, tf);
    }

    /**
     * Evaluate the term feature <code>tf</code> for the term described by the projection
     * <code>term</code>. If <code>term</code> is undefined for a particular rule app, zero is
     * returned
     *
     * @param term term describing the projection
     * @param tf term feature
     * @return feature
     */
    protected static Feature<Goal> applyTFNonStrict(ProjectionToTerm<Goal> term, TermFeature tf) {
        return ApplyTFFeature.createNonStrict(term, tf, NumberRuleAppCost.getZeroCost());
    }

    protected static Feature<Goal> sum(TermBuffer x, TermGenerator gen, Feature<Goal> body) {
        return ComprehendedSumFeature.create(x, gen, body);
    }

    protected static Feature<Goal> let(TermBuffer x, ProjectionToTerm<Goal> value,
            Feature<Goal> body) {
        return LetFeature.create(x, value, body);
    }

    protected static Feature<Goal> isSubSortFeature(ProjectionToTerm<Goal> s1,
            ProjectionToTerm<Goal> s2) {
        return SortComparisonFeature.create(s1, s2, SortComparisonFeature.SUBSORT);
    }

    // Specific features

    protected static Feature<Goal> implicitCastNecessary(ProjectionToTerm<Goal> s1) {
        return ImplicitCastNecessary.create(s1);
    }

    protected static Feature<Goal> isSelectSkolemConstantTerm(String svName) {
        return applyTF(svName, selectSkolemConstantTermFeature());
    }

    protected static TermFeature selectSkolemConstantTermFeature() {
        return add(OperatorClassTF.create(Function.class),
            constantTermFeature(),
            create(ParameterlessTermLabel.SELECT_SKOLEM_LABEL));
    }

    public static TermFeature create(TermLabel label) {
        return TermPredicateTermFeature.create(
            (t -> t instanceof de.uka.ilkd.key.logic.Term jTerm &&
                    jTerm.containsLabel(label)));
    }

    protected static TermFeature anonHeapTermFeature() {
        return add(OperatorClassTF.create(Function.class),
            constantTermFeature(), create(ParameterlessTermLabel.ANON_HEAP_LABEL));
    }

    protected static TermFeature constantTermFeature() {
        return TermPredicateTermFeature
                .create(term -> term.op() instanceof Function && term.arity() == 0);
    }
}
