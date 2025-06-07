/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

public class TriggerVariableInstantiationProjection implements ProjectionToTerm<Goal> {

    @Override
    public JTerm toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert app.rule() instanceof Taclet;
        final Taclet t = (Taclet) app.rule();

        final SVInstantiationProjection instProj =
            SVInstantiationProjection.create(t.getTrigger().triggerVar().name(), true);
        return instProj.toTerm(app, pos, goal, mState);
    }



}
