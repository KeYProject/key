/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
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

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This {@link TermLabelPolicy} maintains a {@link TermLabel} as long the new {@link JTerm} has the
 * same {@link Operator} as the previous best matching {@link JTerm} from which it was created.
 *
 * @author Martin Hentschel
 */
@NullMarked
public class StayOnOperatorTermLabelPolicy implements TermLabelPolicy {
    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable TermLabel keepLabel(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence,
            @Nullable JTerm applicationTerm, Rule rule, @Nullable Goal goal,
            @Nullable Object hint, @Nullable JTerm tacletTerm,
            JTerm newTerm, TermLabel label) {
        return applicationTerm != null
                && JavaDLOperatorUtil.opEquals(newTerm.op(), applicationTerm.op())
                        ? label
                        : null;
    }
}
