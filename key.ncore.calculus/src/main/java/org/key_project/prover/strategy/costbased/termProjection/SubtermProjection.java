/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termProjection;

import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

/// Projection for computing a subterm of a given term. The position of the subterm within the
/// complete term is described using a `PosInTerm`.
public class SubtermProjection<G extends ProofGoal<G>> implements ProjectionToTerm<G> {
    private final PosInTerm pit;
    private final ProjectionToTerm<G> completeTerm;

    public static <G extends ProofGoal<G>> ProjectionToTerm<G> create(
            ProjectionToTerm<G> completeTerm,
            PosInTerm pit) {
        return new SubtermProjection<G>(completeTerm, pit);
    }

    private SubtermProjection(ProjectionToTerm<G> completeTerm, PosInTerm pit) {
        this.completeTerm = completeTerm;
        this.pit = pit;
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, G goal, MutableState mState) {
        return pit.getSubTerm(completeTerm.toTerm(app, pos, goal, mState));
    }
}
