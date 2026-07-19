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

    /** whether the prediction runs with the classic trigger selection */
    private final boolean classicTriggers;

    private InstantiationCost(ProjectionToTerm<Goal> var, boolean classicTriggers) {
        varInst = var;
        this.classicTriggers = classicTriggers;
    }

    public static Feature create(ProjectionToTerm<Goal> varInst, boolean classicTriggers) {
        return new InstantiationCost(varInst, classicTriggers);
    }

    /**
     * Compute the cost of a RuleApp.
     */
    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null : "Projection is only applicable to rules with find";

        final Term formula = pos.sequentFormula().formula();
        final de.uka.ilkd.key.proof.Goal jgoal = (de.uka.ilkd.key.proof.Goal) goal;
        final var instance = varInst.toTerm(app, pos, jgoal, mState);

        return Instantiation.computeCost(instance, formula, goal.sequent(),
            (Services) goal.proof().getServices(), classicTriggers);
    }
}
