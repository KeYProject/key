/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.termProjection.SVInstantiationProjection;

public class TriggerVarInstantiatedFeature extends BinaryTacletAppFeature {

    public static final Feature INSTANCE = new TriggerVarInstantiatedFeature();

    private TriggerVarInstantiatedFeature() {
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        assert app.taclet().hasTrigger();

        SVInstantiationProjection instProj = SVInstantiationProjection
                .create(app.taclet().getTrigger().getTriggerVar().name(), false);

        return instProj.toTerm(app, pos, goal) != null;
    }


}
