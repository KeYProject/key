/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.termProjection.SVInstantiationProjection;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;

public class TriggerVarInstantiatedFeature extends BinaryTacletAppFeature {

    public static final Feature INSTANCE = new TriggerVarInstantiatedFeature();

    private TriggerVarInstantiatedFeature() {
    }

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert app.taclet().hasTrigger();

        SVInstantiationProjection instProj = SVInstantiationProjection
                .create(app.taclet().getTrigger().triggerVar().name(), false);

        return instProj.toTerm(app, pos, goal, mState) != null;
    }


}
