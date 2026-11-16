/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.feature;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.strategy.SeqTermFeatures;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.BinaryFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.StableCost;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/// Feature that checks whether two sequences are built on top of the same base sequences
/// e.g., `seqConcat(s1, seqConcat(seqEmpty, s3))` and `seqSwap(seqConcat(s1,s3), 1, 0)` are
/// constructed from the same base sequences `s1` and `s3`.
@StableCost
public final class SeqSameBasesFeature extends BinaryFeature {
    private final SeqTermFeatures tf;

    private SeqSameBasesFeature(SeqTermFeatures tf) {
        this.tf = tf;
    }

    public static Feature create(SeqTermFeatures tf) {
        return new SeqSameBasesFeature(tf);
    }

    @Override
    protected boolean filter(RuleApp app,
            PosInOccurrence pos, ProofGoal<?> goal, MutableState mState) {
        final LogicServices services = goal.proof().getServices();
        final Term perm = pos.subTerm();
        final Set<Term> left = new LinkedHashSet<>();
        final Set<Term> right = new LinkedHashSet<>();
        collectBaseSequences(perm.sub(0), left, mState, services);
        collectBaseSequences(perm.sub(1), right, mState, services);
        // subset is used as we need to compare the terms modulo renaming
        return isSubset(right, left) && isSubset(left, right);
    }

    private void collectBaseSequences(Term t, Set<Term> baseSequences, MutableState mState,
            LogicServices services) {
        if (isConstructorTerm(t, tf.upd, mState, services)
                || isConstructorTerm(t, tf.swap, mState, services)
                || isConstructorTerm(t, tf.remove, mState, services)) {
            collectBaseSequences(t.sub(0), baseSequences, mState, services);
        } else if (isConstructorTerm(t, tf.concat, mState, services)) {
            collectBaseSequences(t.sub(0), baseSequences, mState, services);
            collectBaseSequences(t.sub(1), baseSequences, mState, services);
        } else if (!isConstructorTerm(t, tf.singleton, mState, services)
                && !isConstructorTerm(t, tf.empty, mState, services)) {
            baseSequences.add(t);
        }
    }

    private static boolean isSubset(Set<Term> subset, Set<Term> superset) {
        return subset.stream().allMatch(
            r -> superset.stream()
                    .anyMatch(t -> RENAMING_TERM_PROPERTY.equalsModThisProperty(t, r)));
    }

    private static boolean isConstructorTerm(Term t, TermFeature constructor,
            MutableState mState, LogicServices services) {
        return !(constructor.compute(t, mState, services) instanceof TopRuleAppCost);
    }
}
