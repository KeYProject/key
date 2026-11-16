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

/// Feature that returns zero iff the trigger variable of the taclet is instantiated, and infinity
/// otherwise.
public class TriggerVarInstantiatedFeature extends BinaryTacletAppFeature {
    public static TriggerVarInstantiatedFeature create() {
        return new TriggerVarInstantiatedFeature();
    }

    private TriggerVarInstantiatedFeature() {
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, ProofGoal<?> goal,
            MutableState mState) {
        final Trigger trigger = app.taclet().getTrigger();
        assert trigger != null : "@AssumeAssertion(nullness): Trigger should not be null";

        SVInstantiationProjection instProj =
            SVInstantiationProjection.create(trigger.triggerVar().name(), false);

        return instProj.toTerm(app, pos, goal, mState) != null;
    }
}
