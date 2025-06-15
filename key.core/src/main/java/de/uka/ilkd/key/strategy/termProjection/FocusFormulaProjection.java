/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

public class FocusFormulaProjection implements ProjectionToTerm<Goal> {

    public static final ProjectionToTerm<Goal> INSTANCE = new FocusFormulaProjection();

    private FocusFormulaProjection() {}

    @Override
    public JTerm toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mutableState) {
        assert pos != null : "Projection is only applicable to rules with find";

        return (JTerm) pos.sequentFormula().formula();
    }

}
