/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Projection of a rule application to its focus (the term or formula that the rule operates on,
 * that for taclets is described using <code>\find</code>, and that can be modified by the rule).
 * Optionally, the projection can walk "upwards" towards the root of the term/formula
 */
public class FocusProjection implements ProjectionToTerm<Goal> {

    public static final ProjectionToTerm<Goal> INSTANCE = create(0);

    private final int stepsUpwards;

    private FocusProjection(int stepsUpwards) {
        assert stepsUpwards >= 0;
        this.stepsUpwards = stepsUpwards;
    }

    public static ProjectionToTerm<Goal> create(int stepsUpwards) {
        return new FocusProjection(stepsUpwards);
    }

    @Override
    public JTerm toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mutableState) {
        assert pos != null : "Projection is only applicable to rules with find";

        int n = stepsUpwards;
        while (n-- > 0 && !pos.isTopLevel()) {
            pos = pos.up();
        }

        return (JTerm) pos.subTerm();
    }

}
