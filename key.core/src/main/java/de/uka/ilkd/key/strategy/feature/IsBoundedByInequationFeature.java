/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.strategy.termgenerator.RelevantSequentFormulasGenerator;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.VolatileCost;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.util.ConcurrentLruCache;
import org.key_project.util.collection.ImmutableList;


/**
 * Checks whether the product of two monomials has the same variables as the left side of
 * an inequation in the sequent. Required to bound the number of cross-multiplications.
 */
@VolatileCost
public final class IsBoundedByInequationFeature extends BinaryTacletAppFeature {

    private final ProjectionToTerm<Goal> mult1;
    private final ProjectionToTerm<Goal> mult2;
    private final RelevantSequentFormulasGenerator inEquations;

    /**
     * cached information about the variables occurring on the left side of an inequation
     * The selected formulas are the secondary cache key: the generator hands out the same list
     * while the goal keeps its sequent, so a new list means the sequent has moved on.
     */
    private record InequationInfo(ImmutableList<Term> selection,
            Set<Map<Term, Integer>> variables) {
    }

    private final Map<Goal, InequationInfo> relations = new ConcurrentLruCache<>(200);

    /**
     * @param mult1 the left side of the first inequation to be multiplied
     * @param mult2 the left side of the second inequation to be multiplied
     * @param inEquationFilter term feature describing the shape of the inequation
     */
    public IsBoundedByInequationFeature(ProjectionToTerm<Goal> mult1, ProjectionToTerm<Goal> mult2,
            TermFeature inEquationFilter) {
        this.mult1 = mult1;
        this.mult2 = mult2;
        this.inEquations = RelevantSequentFormulasGenerator.sequent(inEquationFilter);
    }

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Services services = goal.proof().getServices();
        final Monomial first = Monomial.create(mult1.toTerm(app, pos, goal, mState), services);
        final Monomial second = Monomial.create(mult2.toTerm(app, pos, goal, mState), services);
        return getInEquations(goal, mState).contains(variables(first, second));
    }

    private Set<Map<Term, Integer>> getInEquations(Goal goal, MutableState mState) {
        final ImmutableList<Term> selection = inEquations.selection(goal, mState);
        final InequationInfo cached = relations.get(goal);
        if (cached != null && cached.selection() == selection) {
            return cached.variables();
        }
        final Services services = goal.proof().getServices();
        final Set<Map<Term, Integer>> variables = new HashSet<>();
        for (Term formula : selection) {
            variables.add(variables(Monomial.create(formula.sub(0), services)));
        }
        relations.put(goal, new InequationInfo(selection, variables));
        return variables;
    }

    /**
     * @return how often each variable occurs in the monomial
     */
    private static Map<Term, Integer> variables(Monomial monomial) {
        final Map<Term, Integer> counts = new HashMap<>();
        count(monomial, counts);
        return counts;
    }

    /**
     * @return how often each variable occurs in the product of the two monomials
     */
    private static Map<Term, Integer> variables(Monomial first, Monomial second) {
        final Map<Term, Integer> counts = new HashMap<>();
        count(first, counts);
        count(second, counts);
        return counts;
    }

    private static void count(Monomial monomial, Map<Term, Integer> counts) {
        for (Term part : monomial.getParts()) {
            counts.merge(part, 1, Integer::sum);
        }
    }
}
