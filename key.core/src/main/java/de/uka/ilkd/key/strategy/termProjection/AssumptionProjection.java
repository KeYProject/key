/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;


/**
 * Term projection that delivers the assumptions of a taclet application (the formulas that the
 * \assumes clause of the taclet refers to).
 */
public class AssumptionProjection implements ProjectionToTerm<Goal> {

    private final int no;

    private AssumptionProjection(int no) {
        this.no = no;
    }

    public static ProjectionToTerm<Goal> create(int no) {
        return new AssumptionProjection(no);
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mutableState) {
        assert app instanceof TacletApp
                : "Projection is only applicable to taclet apps," + " but got " + app;
        final TacletApp tapp = (TacletApp) app;

        assert tapp.assumesFormulaInstantiations() != null
                : "Projection is only applicable to taclet apps with assumptions," + " but got "
                    + app;

        return tapp.assumesFormulaInstantiations().take(no).head().getSequentFormula().formula();
    }
}
