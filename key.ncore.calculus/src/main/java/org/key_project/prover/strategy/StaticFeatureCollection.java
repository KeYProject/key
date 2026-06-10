/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.*;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.SVInstantiationProjection;
import org.key_project.prover.strategy.costbased.termProjection.SubtermProjection;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.*;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

/// Collection of strategy features that can be accessed statically. This class is essentially a
/// collection of constructors for various features.
///
/// @author Kai Wallisch \<kai.wallisch@ira.uka.de>
public class StaticFeatureCollection {
    public static Feature longConst(long a) {
        return ConstFeature.createConst(cost(a));
    }

    public static Feature inftyConst() {
        return ConstFeature.createConst(infty());
    }

    public static TermFeature any() {
        return longTermConst(0);
    }

    public static TermFeature longTermConst(long a) {
        return ConstTermFeature.createConst(cost(a));
    }

    public static TermFeature inftyTermConst() {
        return ConstTermFeature.createConst(infty());
    }

    public static Feature add(Feature a, Feature b) {
        return SumFeature.createSum(a, b);
    }

    public static Feature add(Feature a, Feature b, Feature c) {
        return SumFeature.createSum(a, b, c);
    }

    @SafeVarargs
    public static Feature add(Feature... features) {
        return SumFeature.createSum(features);
    }

    public static TermFeature add(TermFeature a, TermFeature b) {
        return BinarySumTermFeature.createSum(a, b);
    }

    public static <G extends ProofGoal<G>> Feature sum(TermBuffer<G> x, TermGenerator<G> gen,
            Feature body) {
        return ComprehendedSumFeature.create(x, gen, body);
    }

    public static TermFeature add(TermFeature a, TermFeature b, TermFeature c) {
        // could be done more efficiently
        return add(a, add(b, c));
    }

    public static TermFeature or(TermFeature a, TermFeature b) {
        return ifZero(a, longTermConst(0), b);
    }

    public static TermFeature or(TermFeature a, TermFeature b, TermFeature c) {
        return or(a, or(b, c));
    }

    public static TermFeature or(TermFeature... features) {
        TermFeature orFeature = inftyTermConst();
        for (var f : features) {
            orFeature = or(orFeature, f);
        }
        return orFeature;
    }

    public static Feature or(Feature a, Feature b) {
        return ifZero(a, longConst(0), b);
    }

    public static Feature or(Feature a, Feature b, Feature c) {
        return or(a, or(b, c));
    }

    @SafeVarargs
    public static Feature or(Feature... features) {
        Feature orFeature = inftyConst();
        for (Feature f : features) {
            orFeature = or(orFeature, f);
        }
        return orFeature;
    }

    public static Feature ifZero(Feature cond, Feature thenFeature) {
        return ShannonFeature.createConditionalBinary(cond, thenFeature);
    }

    public static Feature ifZero(Feature cond, Feature thenFeature,
            Feature elseFeature) {
        return ShannonFeature.createConditionalBinary(cond, thenFeature, elseFeature);
    }

    public static TermFeature ifZero(TermFeature cond, TermFeature thenFeature) {
        return ShannonTermFeature.createConditionalBinary(cond, thenFeature);
    }

    public static TermFeature ifZero(TermFeature cond, TermFeature thenFeature,
            TermFeature elseFeature) {
        return ShannonTermFeature.createConditionalBinary(cond, thenFeature, elseFeature);
    }

    public static Feature not(Feature f) {
        return ifZero(f, inftyConst(), longConst(0));
    }

    public static TermFeature not(TermFeature f) {
        return ifZero(f, ConstTermFeature.createConst(TopRuleAppCost.INSTANCE), longTermConst(0));
    }

    public static Feature eq(Feature a, Feature b) {
        return CompareCostsFeature.eq(a, b);
    }

    public static <G extends ProofGoal<G>> Feature eq(ProjectionToTerm<G> t1,
            ProjectionToTerm<G> t2,
            java.util.function.Function<TermBuffer<G>, TermFeature> createEqTermFeature) {
        final TermBuffer<G> buf = new TermBuffer<>();
        return let(buf, t1, applyTF(t2, createEqTermFeature.apply(buf)));
    }

    public static Feature less(Feature a, Feature b) {
        return CompareCostsFeature.less(a, b);
    }

    public static Feature leq(Feature a, Feature b) {
        return CompareCostsFeature.leq(a, b);
    }

    public static RuleAppCost cost(long p) {
        return NumberRuleAppCost.create(p);
    }

    private static RuleAppCost infty() {
        return TopRuleAppCost.INSTANCE;
    }

    /// Create a projection of taclet applications to the instantiation of the schema variables
    /// `schemaVar`. If `schemaVar` is not instantiated for a particular taclet
    /// app, an error will be raised
    ///
    /// @param schemaVar schema variable
    /// @return projection of taclet applications
    public static <G extends ProofGoal<G>> ProjectionToTerm<G> instOf(String schemaVar) {
        return SVInstantiationProjection.create(new Name(schemaVar), true);
    }

    /// Create a projection of taclet applications to the instantiation of the schema variables
    /// `schemaVar`. The projection will be partial and undefined for those taclet
    /// applications that do not instantiate `schemaVar`
    ///
    /// @param schemaVar schema variable
    /// @return projection of taclet applications
    public static <G extends ProofGoal<G>> ProjectionToTerm<G> instOfNonStrict(
            String schemaVar) {
        return SVInstantiationProjection.create(new Name(schemaVar), false);
    }

    public static TermFeature op(Operator op) {
        return OperatorTF.create(op);
    }

    public static TermFeature rec(TermFeature cond, TermFeature summand) {
        return RecSubTermFeature.create(cond, summand);
    }

    public static <G extends ProofGoal<G>> ProjectionToTerm<G> subAt(ProjectionToTerm<G> t,
            PosInTerm pit) {
        return SubtermProjection.create(t, pit);
    }

    public static TermFeature sub(TermFeature sub0) {
        return SubTermFeature.create(new TermFeature[] { sub0 });
    }

    public static TermFeature sub(TermFeature sub0, TermFeature sub1) {
        return SubTermFeature.create(new TermFeature[] { sub0, sub1 });
    }

    public static <G extends ProofGoal<G>> ProjectionToTerm<G> sub(ProjectionToTerm<G> t,
            int index) {
        return SubtermProjection.create(t, PosInTerm.getTopLevel().down(index));
    }

    public static TermFeature opSub(Operator op, TermFeature sub0) {
        return add(op(op), sub(sub0));
    }

    public static TermFeature opSub(Operator op, TermFeature sub0, TermFeature sub1) {
        return add(op(op), sub(sub0, sub1));
    }

    public static <G extends ProofGoal<G>> Feature contains(ProjectionToTerm<G> bigTerm,
            ProjectionToTerm<G> searchedTerm,
            java.util.function.Function<TermBuffer<G>, TermFeature> createEqTermFeature) {
        final TermBuffer<G> buf = new TermBuffer<>();
        return let(buf, searchedTerm,
            applyTF(bigTerm, not(rec(any(), not(createEqTermFeature.apply(buf))))));
    }

    public static <G extends ProofGoal<G>> Feature let(TermBuffer<G> x,
            ProjectionToTerm<G> value,
            Feature body) {
        return LetFeature.create(x, value, body);
    }

    public static <G extends ProofGoal<G>> Feature println(ProjectionToTerm<G> t) {
        return applyTF(t, PrintTermFeature.INSTANCE);
    }

    public static TermFeature extendsTrans(Sort s) {
        return SortExtendsTransTermFeature.create(s);
    }

    /// Invoke the term feature `tf` on the term that instantiation of
    /// `schemaVar`. This is the strict/safe version that raises an error of
    /// `schemaVar` is not instantiated for a particular taclet app
    ///
    /// @param schemaVar schema variable
    /// @param tf term feature
    /// @return feature
    public static <G extends ProofGoal<G>> Feature applyTF(String schemaVar, TermFeature tf) {
        return applyTF(StaticFeatureCollection.<G>instOf(schemaVar), tf);
    }

    /// Invoke the term feature `tf` on the term that instantiation of
    /// `schemaVar`. This is the non-strict/unsafe version that simply returns zero if
    /// `schemaVar` is not instantiated for a particular taclet app
    ///
    /// @param schemaVar schema variable
    /// @param tf term feature
    /// @return feature
    public static <G extends ProofGoal<G>> Feature applyTFNonStrict(String schemaVar,
            TermFeature tf) {
        return applyTFNonStrict(StaticFeatureCollection.<G>instOfNonStrict(schemaVar), tf);
    }

    /// Evaluate the term feature `tf` for the term described by the projection
    /// `term`. If `term` is undefined for a particular rule app, an exception
    /// is raised
    ///
    /// @param term term describing the projection
    /// @param tf term feature
    /// @return feature
    public static <G extends ProofGoal<G>> Feature applyTF(ProjectionToTerm<G> term,
            TermFeature tf) {
        return ApplyTFFeature.create(term, tf);
    }

    /// Evaluate the term feature `tf` for the term described by the projection
    /// `term`. If `term` is undefined for a particular rule app, zero is
    /// returned
    ///
    /// @param term term describing the projection
    /// @param tf term feature
    /// @return feature
    public static <G extends ProofGoal<G>> Feature applyTFNonStrict(ProjectionToTerm<G> term,
            TermFeature tf) {
        return ApplyTFFeature.createNonStrict(term, tf, NumberRuleAppCost.getZeroCost());
    }

    public static TermFeature constantTermFeature() {
        return TermPredicateTermFeature
                .create(term -> term.op() instanceof Function && term.arity() == 0);
    }

    public static Feature isInstantiated(String schemaVar) {
        return InstantiatedSVFeature.create(new Name(schemaVar));
    }
}
