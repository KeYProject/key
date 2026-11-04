/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.rules.Trigger;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.SVInstantiationProjection;

import org.jspecify.annotations.Nullable;

@StableCost
public class TriggerVariableInstantiationProjection<GOAL extends ProofGoal<GOAL>>
        implements ProjectionToTerm<GOAL> {
    @Override
    public @Nullable Term toTerm(RuleApp app, PosInOccurrence pos, GOAL goal,
            MutableState mState) {
        assert app.rule() instanceof Taclet;
        final Taclet t = (Taclet) app.rule();
        final Trigger trigger = t.getTrigger();
        assert trigger != null : "@AssumeAssertion(nullness): Trigger should not be null";

        final SVInstantiationProjection<GOAL> instProj =
            SVInstantiationProjection.create(trigger.triggerVar().name(), true);
        return instProj.toTerm(app, pos, goal, mState);
    }
}
