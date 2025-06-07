/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.JavaDLOperatorUtil;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.op.Operator;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.sequent.PosInOccurrence;

/**
 * This {@link TermLabelPolicy} maintains a {@link TermLabel} as long the new {@link JTerm} has the
 * same {@link Operator} as the previous best matching {@link JTerm} from which it was created.
 *
 * @author Martin Hentschel
 */
public class StayOnOperatorTermLabelPolicy implements TermLabelPolicy {
    /**
     * {@inheritDoc}
     */
    @Override
    public TermLabel keepLabel(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, JTerm applicationTerm, Rule rule, Goal goal,
            Object hint, JTerm tacletTerm,
            JTerm newTerm, TermLabel label) {
        return applicationTerm != null
                && JavaDLOperatorUtil.opEquals(newTerm.op(), applicationTerm.op())
                        ? label
                        : null;
    }
}
