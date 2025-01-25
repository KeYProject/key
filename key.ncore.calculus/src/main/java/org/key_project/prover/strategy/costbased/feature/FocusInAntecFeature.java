/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

import org.jspecify.annotations.NonNull;

public class FocusInAntecFeature<Goal extends ProofGoal<@NonNull Goal>>
        extends BinaryFeature<Goal> {

    private static final Feature<?> INSTANCE = new FocusInAntecFeature<>();


    private FocusInAntecFeature() {}

    public static <Goal extends ProofGoal<@NonNull Goal>> Feature<Goal> getInstance() {
        // noinspection unchecked
        return (Feature<Goal>) INSTANCE;
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";
        return pos.isInAntec();
    }
}
