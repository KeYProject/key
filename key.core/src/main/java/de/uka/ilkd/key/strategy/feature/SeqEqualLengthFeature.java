/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.feature;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;
import de.uka.ilkd.key.strategy.SeqTermFeatures;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.BinaryFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// Determines whether the equality of the length of two sequences can be easily derived from their
/// syntactic form
public final class SeqEqualLengthFeature extends BinaryFeature {
    private final ProjectionToTerm<Goal> first;
    private final ProjectionToTerm<Goal> second;
    private final SeqTermFeatures tf;

    private SeqEqualLengthFeature(ProjectionToTerm<Goal> first, ProjectionToTerm<Goal> second,
            SeqTermFeatures tf) {
        this.first = first;
        this.second = second;
        this.tf = tf;
    }

    /// @param first the projection to the first sequence
    /// @param second the projection to the second sequence
    /// @param tf the term features of the sequence theories
    /// @return the feature
    public static Feature create(ProjectionToTerm<Goal> first, ProjectionToTerm<Goal> second,
            SeqTermFeatures tf) {
        return new SeqEqualLengthFeature(first, second, tf);
    }

    @Override
    protected <G extends ProofGoal<@NonNull G>> boolean filter(RuleApp app,
            PosInOccurrence pos, G goal, MutableState mState) {
        final Goal g = (Goal) goal;
        final Services services = g.proof().getServices();
        final Polynomial firstAsPoly = length(first.toTerm(app, pos, g, mState), mState, services);
        final Polynomial secondAsPoly =
            length(second.toTerm(app, pos, g, mState), mState, services);
        return firstAsPoly != null && secondAsPoly != null && firstAsPoly.valueEq(secondAsPoly);
    }

    /// determine the length of the given sequence or `null` if it cannot be determined
    /// (uniquely, e.g. the length of `seqRemove(seq, e)` depends on whether `e` is in
    /// `seq` or not, hence, `null` is returned here).
    private @Nullable Polynomial length(Term seq, MutableState mState, Services services) {
        if (isConstructorTerm(seq, tf.empty, mState, services)) {
            return Polynomial.ZERO;
        } else if (isConstructorTerm(seq, tf.singleton, mState, services)) {
            return Polynomial.ZERO.add(BigInteger.ONE);
        } else if (isConstructorTerm(seq, tf.concat, mState, services)) {
            final Polynomial a = length(seq.sub(0), mState, services);
            final Polynomial b = length(seq.sub(1), mState, services);
            return a == null || b == null ? null : a.add(b);
        } else if (isConstructorTerm(seq, tf.def, mState, services)) {
            return Polynomial.create(seq.sub(1), services)
                    .sub(Polynomial.create(seq.sub(0), services));
        } else if (isConstructorTerm(seq, tf.subSequence, mState, services)) {
            return Polynomial.create(seq.sub(2), services)
                    .sub(Polynomial.create(seq.sub(1), services));
        } else if (isConstructorTerm(seq, tf.upd, mState, services)
                || isConstructorTerm(seq, tf.swap, mState, services)
                || isConstructorTerm(seq, tf.reverse, mState, services)) {
            return length(seq.sub(0), mState, services);
        } else if (isConstructorTerm(seq, tf.remove, mState, services)
                || isConstructorTerm(seq, tf.nPermInv, mState, services)) {
            return null;
        }
        return Polynomial.create(seq, services);
    }

    private static boolean isConstructorTerm(Term seq, TermFeature constructor,
            MutableState mState, Services services) {
        return !(constructor.compute(seq, mState, services) instanceof TopRuleAppCost);
    }
}
