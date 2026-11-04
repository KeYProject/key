/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.SVInstantiationProjection;

/// Feature that returns zero iff a certain schema variable is instantiated. If the schemavariable
/// is
/// not instantiated schema variable or does not occur in the taclet infinity costs are returned.
///
/// [StableCost]: the instantiation is read from the rule application's own instantiations, not
/// from the goal, so the result is fixed for a given application.
@StableCost
public class InstantiatedSVFeature<GOAL extends ProofGoal<GOAL>>
        extends BinaryTacletAppFeature<GOAL> {
    private final ProjectionToTerm<GOAL> instProj;

    public static Feature create(Name svName) {
        return new InstantiatedSVFeature<>(svName);
    }

    protected InstantiatedSVFeature(Name svName) {
        instProj = SVInstantiationProjection.create(svName, false);
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, GOAL goal, MutableState mState) {
        return instProj.toTerm(app, pos, goal, mState) != null;
    }
}
