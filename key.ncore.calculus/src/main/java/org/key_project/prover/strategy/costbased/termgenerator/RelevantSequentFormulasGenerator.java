/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.termgenerator;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.VolatileCost;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.util.ConcurrentLruCache;
import org.key_project.util.collection.ImmutableList;

/**
 * Enumerates the formulas of the sequent that satisfy a term feature.
 */
@VolatileCost
public final class RelevantSequentFormulasGenerator<G extends ProofGoal<G>>
        implements TermGenerator<G> {

    /** Specifies whether to iterate over all formulas or only one of those of one semisequent */
    private enum SequentScope {
        SEQUENT, ANTECEDENT, SUCCEDENT
    }

    private final SequentScope part;

    private final TermFeature accepted;


    /**
     * Secondary cache key to invalidate a cache hit if goal's sequent has changed
     * (compared by identity). The cache is for reuse of
     * many rule applications candidates on one goal for one proof step
     */
    private record Selection(Sequent sequent, ImmutableList<Term> formulas) {
    }

    /**
     * Caching of selected formulas to be iterated over (second key for cache is in Selection)
     */
    private final Map<G, Selection> selections = new ConcurrentLruCache<>(200);

    private RelevantSequentFormulasGenerator(SequentScope part, TermFeature accepted) {
        this.part = part;
        this.accepted = accepted;
    }

    /**
     * @param filter the TermFeature used to filter the formulas of the sequent
     * @return the formulas of the sequent the feature accepts
     */
    public static <G extends ProofGoal<G>> RelevantSequentFormulasGenerator<G> sequent(
            TermFeature filter) {
        return new RelevantSequentFormulasGenerator<>(SequentScope.SEQUENT, filter);
    }

    /**
     * @param filter the TermFeature used to filter the formulas of the sequent
     * @return the formulas of the antecedent the feature accepts
     */
    public static <G extends ProofGoal<G>> RelevantSequentFormulasGenerator<G> antecedent(
            TermFeature filter) {
        return new RelevantSequentFormulasGenerator<>(SequentScope.ANTECEDENT, filter);
    }

    /**
     * @param filter the TermFeature used to filter the formulas of the sequent
     * @return the formulas of the succedent the feature accepts
     */
    public static <G extends ProofGoal<G>> RelevantSequentFormulasGenerator<G> succedent(
            TermFeature filter) {
        return new RelevantSequentFormulasGenerator<>(SequentScope.SUCCEDENT, filter);
    }

    /**
     * The formulas the filter accepts. The same list is returned while the goal keeps its sequent,
     * so a caller that derives something from the selection can hold that result and reuse it for
     * as long as it is handed the same list.
     *
     * @param goal the goal whose formulas are selected
     * @param mState the state the filter is evaluated in
     * @return the accepted formulas
     */
    public ImmutableList<Term> selection(G goal, MutableState mState) {
        final Sequent sequent = goal.sequent();
        final Selection cached = selections.get(goal);
        if (cached != null && cached.sequent() == sequent) {
            return cached.formulas();
        }
        final ImmutableList<Term> formulas = ImmutableList.fromList(select(goal, mState));
        selections.put(goal, new Selection(sequent, formulas));
        return formulas;
    }

    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, G goal,
            MutableState mState) {
        return selection(goal, mState).iterator();
    }

    private List<Term> select(G goal, MutableState mState) {
        final var services = goal.proof().getServices();
        final List<Term> formulas = new ArrayList<>();
        final Iterable<SequentFormula> source = switch (part) {
            case SEQUENT -> goal.sequent();
            case ANTECEDENT -> goal.sequent().antecedent();
            case SUCCEDENT -> goal.sequent().succedent();
        };
        for (SequentFormula sf : source) {
            final Term formula = sf.formula();
            if (!(accepted.compute(formula, mState, services) instanceof TopRuleAppCost)) {
                formulas.add(formula);
            }
        }
        return formulas;
    }
}
