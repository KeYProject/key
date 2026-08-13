/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
public class InstantiatedSVFeature<G extends ProofGoal<G>> extends BinaryTacletAppFeature<G> {

    private final ProjectionToTerm<G> instProj;

    public static <G extends ProofGoal<G>> Feature create(Name svName) {
        return new InstantiatedSVFeature<G>(svName);
    }

    protected InstantiatedSVFeature(Name svName) {
        instProj = SVInstantiationProjection.create(svName, false);
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, G goal, MutableState mState) {
        return instProj.toTerm(app, pos, goal, mState) != null;
    }
}
