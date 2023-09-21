/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Binary features that returns zero iff the if-formulas of a Taclet are instantiated or the Taclet
 * does not have any if-formulas.
 */
public final class MatchedIfFeature extends BinaryTacletAppFeature {

    public static final Feature INSTANCE = new MatchedIfFeature();

    private MatchedIfFeature() {}

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        return app.ifInstsComplete();
    }

}
