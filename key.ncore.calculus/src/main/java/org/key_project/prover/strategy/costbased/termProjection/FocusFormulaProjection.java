/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.termProjection;


import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.WeakStableCost;

// WeakStable, not Stable: returns the whole find formula (pos.sequentFormula().formula()), i.e.
// it reads above the find subterm -- valid only while that formula is unchanged.
@WeakStableCost
public class FocusFormulaProjection<GOAL extends ProofGoal<GOAL>>
        implements ProjectionToTerm<GOAL> {


    public static <GOAL extends ProofGoal<GOAL>> FocusFormulaProjection<GOAL> create() {
        return new FocusFormulaProjection<>();
    }

    private FocusFormulaProjection() {}

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, GOAL goal, MutableState mutableState) {
        assert pos != null : "Projection is only applicable to rules with find";

        return pos.sequentFormula().formula();
    }

}
