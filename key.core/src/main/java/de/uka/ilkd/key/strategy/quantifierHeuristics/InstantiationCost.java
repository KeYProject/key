/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Feature that returns the number of branches after instantiated the quantifier formula.
 */
public class InstantiationCost implements Feature<Goal> {

    final private ProjectionToTerm varInst;

    private InstantiationCost(ProjectionToTerm var) {
        varInst = var;
    }

    public static Feature<Goal> create(ProjectionToTerm varInst) {
        return new InstantiationCost(varInst);
    }

    /**
     * Compute the cost of a RuleApp.
     */
    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        assert pos != null : "Projection is only applicable to rules with find";

        final Term formula = (Term) pos.sequentFormula().formula();
        final var instance = varInst.toTerm(app, pos, goal, mState);

        return Instantiation.computeCost(instance, formula, goal.sequent(),
            goal.proof().getServices());
    }
}
