/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

/**
 * Feature that returns the number of branches after instantiated the quantifier formula.
 */
public class InstantiationCost implements Feature {

    final private ProjectionToTerm varInst;

    private InstantiationCost(ProjectionToTerm var) {
        varInst = var;
    }

    public static Feature create(ProjectionToTerm varInst) {
        return new InstantiationCost(varInst);
    }

    /**
     * Compute the cost of a RuleApp.
     */
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Projection is only applicable to rules with find";

        final Term formula = pos.sequentFormula().formula();
        final Term instance = varInst.toTerm(app, pos, goal);

        return Instantiation.computeCost(instance, formula, goal.sequent(),
            goal.proof().getServices());
    }
}
