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

/**
 * Projection of a rule application to its focus (the term or formula that the rule operates on,
 * that for taclets is described using <code>\find</code>, and that can be modified by the rule).
 * Optionally, the projection can walk "upwards" towards the root of the term/formula
 */
// WeakStable, not Stable: with stepsUpwards > 0 (e.g. FocusProjection.create(1)) this walks up
// from the find subterm, so it reads the surrounding find formula -- valid only while that
// formula is unchanged.
@WeakStableCost
public class FocusProjection<Goal extends ProofGoal<Goal>> implements ProjectionToTerm<Goal> {

    private final int stepsUpwards;

    private FocusProjection(int stepsUpwards) {
        assert stepsUpwards >= 0;
        this.stepsUpwards = stepsUpwards;
    }

    public static <Goal extends ProofGoal<Goal>> ProjectionToTerm<Goal> create() {
        return create(0);
    }

    public static <Goal extends ProofGoal<Goal>> ProjectionToTerm<Goal> create(int stepsUpwards) {
        return new FocusProjection(stepsUpwards);
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mutableState) {
        assert pos != null : "Projection is only applicable to rules with find";

        int n = stepsUpwards;
        while (n-- > 0 && !pos.isTopLevel()) {
            pos = pos.up();
        }

        return pos.subTerm();
    }

}
