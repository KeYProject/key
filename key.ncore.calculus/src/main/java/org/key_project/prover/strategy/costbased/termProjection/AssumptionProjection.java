/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termProjection;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

/// Term projection that delivers the assumptions of a taclet application (the formulas that the
/// \assumes clause of the taclet refers to).
public class AssumptionProjection<G extends ProofGoal<G>> implements ProjectionToTerm<G> {

    private final int no;

    private AssumptionProjection(int no) {
        this.no = no;
    }

    public static <G extends ProofGoal<G>> ProjectionToTerm<G> create(int no) {
        return new AssumptionProjection(no);
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, G goal, MutableState mutableState) {
        assert app instanceof ITacletApp
                : "Projection is only applicable to taclet apps," + " but got " + app;
        final var tapp = (ITacletApp) app;

        assert tapp.assumesFormulaInstantiations() != null
                : "Projection is only applicable to taclet apps with assumptions,"
                    + " but got "
                    + app;

        return tapp.assumesFormulaInstantiations().skip(no).head().getSequentFormula().formula();
    }
}
