/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.feature.MutableState;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class TriggerVariableInstantiationProjection implements ProjectionToTerm {

    @Override
    public @Nullable Term toTerm(@NonNull RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert app.rule() instanceof Taclet;
        final Taclet t = (Taclet) app.rule();

        final SVInstantiationProjection instProj =
            SVInstantiationProjection.create(t.getTrigger().triggerVar().name(), true);
        return instProj.toTerm(app, pos, goal, mState);
    }



}
