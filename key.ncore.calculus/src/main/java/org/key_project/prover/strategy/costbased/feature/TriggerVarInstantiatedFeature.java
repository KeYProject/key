/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.rules.Trigger;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.SVInstantiationProjection;

public class TriggerVarInstantiatedFeature<GOAL extends ProofGoal<GOAL>>
        extends BinaryTacletAppFeature<GOAL> {

    public static <GOAL extends ProofGoal<GOAL>> TriggerVarInstantiatedFeature<GOAL> create() {
        return new TriggerVarInstantiatedFeature<>();
    }

    private TriggerVarInstantiatedFeature() {
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, GOAL goal,
            MutableState mState) {
        final Trigger trigger = app.taclet().getTrigger();
        assert trigger != null : "@AssumeAssertion(nullness): Trigger should not be null";

        SVInstantiationProjection<GOAL> instProj =
            SVInstantiationProjection.create(trigger.triggerVar().name(), false);

        return instProj.toTerm(app, pos, goal, mState) != null;
    }


}
