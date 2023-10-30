/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Projection of a rule application to its focus (the term or formula that the rule operates on,
 * that for taclets is described using <code>\find</code>, and that can be modified by the rule).
 * Optionally, the projection can walk "upwards" towards the root of the term/formula
 */
public class FocusProjection implements ProjectionToTerm {

    public static final ProjectionToTerm INSTANCE = create(0);

    private final int stepsUpwards;

    private FocusProjection(int stepsUpwards) {
        assert stepsUpwards >= 0;
        this.stepsUpwards = stepsUpwards;
    }

    public static ProjectionToTerm create(int stepsUpwards) {
        return new FocusProjection(stepsUpwards);
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Projection is only applicable to rules with find";

        int n = stepsUpwards;
        while (n-- > 0 && !pos.isTopLevel()) {
            pos = pos.up();
        }

        return pos.subTerm();
    }

}
