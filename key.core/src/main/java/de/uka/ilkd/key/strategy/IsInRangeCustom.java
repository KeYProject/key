/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

public class IsInRangeCustom extends IsInRangeProvable {

    private final ProjectionToTerm left;
    private final ProjectionToTerm right;

    public static IsInRangeCustom create(ProjectionToTerm left, ProjectionToTerm right) {
        return new IsInRangeCustom(left, right);
    }

    private IsInRangeCustom(ProjectionToTerm left, ProjectionToTerm right) {
        super(250, 5000);
        this.left = left;
        this.right = right;
    }

    @Override
    protected Term createConsequence(RuleApp app,
            PosInOccurrence pos, Goal goal) {
        final TermBuilder tb = goal.proof().getServices().getTermBuilder();
        Term t_left = left.toTerm(app, pos, goal);
        Term t_right = right.toTerm(app, pos, goal);
        return tb.gt(t_left, t_right);
    }


}
