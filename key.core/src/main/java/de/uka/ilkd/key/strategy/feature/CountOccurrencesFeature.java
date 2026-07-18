/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.JTerm;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

import org.jspecify.annotations.NonNull;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * Counts how often a given term occurs in the sequent: the returned cost is the number of
 * positions, over all formulas of the goal's sequent and all their subterms, whose term is equal
 * to the given term up to renaming of bound variables. Used by the splitting heuristics to
 * prefer cutting over formulas that occur often.
 *
 * <p>
 * The count is computed directly instead of with a comprehension over all subterms
 * ({@code sum(sf, sequent, sum(sub, subterms(sf), ...))}): two terms that are equal up to
 * renaming have the same depth, so subterms whose depth differs from the target's cannot be
 * occurrences, and subterms shallower than the target cannot contain one either. The walk
 * therefore only descends while a node is deeper than the target and only compares nodes of
 * exactly the target's depth. On large sequents this skips almost the whole traversal; the
 * counted result is the same. ({@link Term#depth()} is cached on the term, so the guard costs a
 * field read.)
 *
 * <p>
 * If the projection has no value (its schema variable is not instantiated), the result is
 * {@link TopRuleAppCost}, as with the comprehension it replaces.
 */
public class CountOccurrencesFeature<Goal extends ProofGoal<@NonNull Goal>> implements Feature {

    private final ProjectionToTerm<Goal> target;

    private CountOccurrencesFeature(ProjectionToTerm<Goal> target) {
        this.target = target;
    }

    public static <Goal extends ProofGoal<@NonNull Goal>> Feature create(
            ProjectionToTerm<Goal> target) {
        return new CountOccurrencesFeature<>(target);
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
            count += occurrences(sf.formula(), (JTerm) targetTerm, targetDepth);
        }
        return NumberRuleAppCost.create(count);
    }

    private static long occurrences(Term t, JTerm target, int targetDepth) {
        final int depth = t.depth();
        if (depth < targetDepth) {
            // t and all its subterms are too shallow to be an occurrence
            return 0;
        }
        if (depth == targetDepth) {
            // subterms of t are shallower than the target, so only t itself can match
            return RENAMING_TERM_PROPERTY.equalsModThisProperty(t, target) ? 1 : 0;
        }
        long count = 0;
        for (int i = 0, n = t.arity(); i < n; i++) {
            count += occurrences(t.sub(i), target, targetDepth);
        }
        return count;
    }
}
