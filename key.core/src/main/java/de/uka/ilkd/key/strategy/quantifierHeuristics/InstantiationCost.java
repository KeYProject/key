/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

import org.jspecify.annotations.NonNull;

/**
 * Feature that returns the number of branches after instantiated the quantifier formula.
 */
public class InstantiationCost implements Feature {

    final private ProjectionToTerm<Goal> varInst;

    private InstantiationCost(ProjectionToTerm<Goal> var) {
        varInst = var;
    }

    public static Feature create(ProjectionToTerm<Goal> varInst) {
        return new InstantiationCost(varInst);
    }

    /**
     * Compute the cost of a RuleApp.
     */
    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null : "Projection is only applicable to rules with find";

        final Term formula = pos.sequentFormula().formula();
        final var instance = varInst.toTerm(app, pos, (de.uka.ilkd.key.proof.Goal) goal, mState);

        return Instantiation.computeCost(instance, formula, goal.sequent(),
            (Services) goal.proof().getServices());
    }
}
