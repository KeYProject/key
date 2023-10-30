/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;


/**
 * Term projection that delivers the assumptions of a taclet application (the formulas that the
 * \assumes clause of the taclet refers to).
 */
public class AssumptionProjection implements ProjectionToTerm {

    private final int no;

    private AssumptionProjection(int no) {
        this.no = no;
    }

    public static ProjectionToTerm create(int no) {
        return new AssumptionProjection(no);
    }

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert app instanceof TacletApp
                : "Projection is only applicable to taclet apps," + " but got " + app;
        final TacletApp tapp = (TacletApp) app;

        assert tapp.ifFormulaInstantiations() != null
                : "Projection is only applicable to taclet apps with assumptions," + " but got "
                    + app;

        return tapp.ifFormulaInstantiations().take(no).head().getConstrainedFormula().formula();
    }
}
