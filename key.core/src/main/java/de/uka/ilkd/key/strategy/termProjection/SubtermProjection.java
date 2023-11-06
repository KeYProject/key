/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Projection for computing a subterm of a given term. The position of the subterm within the
 * complete term is described using a <code>PosInTerm</code>.
 */
public class SubtermProjection implements ProjectionToTerm {

    private final PosInTerm pit;
    private final ProjectionToTerm completeTerm;

    public static ProjectionToTerm create(ProjectionToTerm completeTerm, PosInTerm pit) {
        return new SubtermProjection(completeTerm, pit);
    }

    private SubtermProjection(ProjectionToTerm completeTerm, PosInTerm pit) {
        this.completeTerm = completeTerm;
        this.pit = pit;
    }

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        return pit.getSubTerm(completeTerm.toTerm(app, pos, goal));
    }
}
