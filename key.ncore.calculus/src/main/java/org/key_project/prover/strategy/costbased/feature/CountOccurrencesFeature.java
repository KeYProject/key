/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.logic.Property;
import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

import org.jspecify.annotations.NonNull;

/// Counts how often a given term occurs in the sequent: the returned cost is the number of
/// to the given term modulo `equalsProp`. Used by the splitting heuristics to prefer cutting
/// over formulas that occur often.
///
/// The count is computed directly instead of with a comprehension over all subterms
/// (`sum(sf, sequent, sum(sub, subterms(sf), ...))`): two terms that are equal
/// up to `equalsProp` have the same depth, so subterms whose depth differs from the target's
/// cannot be occurrences, and subterms shallower than the target cannot contain one either. The
/// walk
/// therefore only descends while a node is deeper than the target and only compares nodes of
/// exactly the target's depth. On large sequents this skips almost the whole traversal; the
/// counted result is the same. ([Term#depth()] is cached on the term, so the guard costs a
/// field read.)
///
/// If the projection has no value (its schema variable is not instantiated), the result is
/// [TopRuleAppCost], as with the comprehension it replaces.
public class CountOccurrencesFeature<Goal extends ProofGoal<@NonNull Goal>> implements Feature {
    private final ProjectionToTerm target;
    private final Property<Term> equalsProp;

    private CountOccurrencesFeature(ProjectionToTerm target, Property<Term> equalsProp) {
        this.equalsProp = equalsProp;
        this.target = target;
    }

    public static <Goal extends ProofGoal<@NonNull Goal>> Feature create(
            ProjectionToTerm target, Property<Term> equalsProp) {
        return new CountOccurrencesFeature<Goal>(target, equalsProp);
    }

    @SuppressWarnings("unchecked")
    @Override
    public <G extends ProofGoal<@NonNull G>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, G goal, MutableState mState) {
        final Term targetTerm = target.toTerm(app, pos, (Goal) goal, mState);
        if (targetTerm == null) {
            assert false : "CountOccurrencesFeature: got undefined argument (null)";
            return TopRuleAppCost.INSTANCE;
        }
        final int targetDepth = targetTerm.depth();
        long count = 0;
        for (final SequentFormula sf : goal.sequent()) {
            count += occurrences(sf.formula(), targetTerm, targetDepth, equalsProp);
        }
        return NumberRuleAppCost.create(count);
    }

    private static long occurrences(Term t, Term target, int targetDepth, Property<Term> cmp) {
        final int depth = t.depth();
        if (depth < targetDepth) {
            // t and all its subterms are too shallow to be an occurrence
            return 0;
        }
        if (depth == targetDepth) {
            // subterms of t are shallower than the target, so only t itself can match
            return cmp.equalsModThisProperty(t, target) ? 1 : 0;
        }
        long count = 0;
        for (int i = 0, n = t.arity(); i < n; i++) {
            count += occurrences(t.sub(i), target, targetDepth, cmp);
        }
        return count;
    }
}
