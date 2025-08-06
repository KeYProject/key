/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Projection for computing a subterm of a given term. The position of the subterm within the
 * complete term is described using a <code>PosInTerm</code>.
 */
public class SubtermProjection implements ProjectionToTerm<Goal> {

    private final PosInTerm pit;
    private final ProjectionToTerm<Goal> completeTerm;

    public static ProjectionToTerm<Goal> create(ProjectionToTerm<Goal> completeTerm,
            PosInTerm pit) {
        return new SubtermProjection(completeTerm, pit);
    }

    private SubtermProjection(ProjectionToTerm<Goal> completeTerm, PosInTerm pit) {
        this.completeTerm = completeTerm;
        this.pit = pit;
    }

    @Override
    public JTerm toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        return (JTerm) pit.getSubTerm(completeTerm.toTerm(app, pos, goal, mState));
    }
}
