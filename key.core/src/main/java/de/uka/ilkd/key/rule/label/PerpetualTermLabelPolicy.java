/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.Rule;
import org.key_project.prover.sequent.PosInOccurrence;

/**
 * This policy always maintains a label.
 *
 * @author lanzinger
 */
public class PerpetualTermLabelPolicy implements TermLabelPolicy {

    @Override
    public TermLabel keepLabel(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, JTerm applicationTerm, Rule rule, Goal goal,
            Object hint, JTerm tacletTerm,
            JTerm newTerm, TermLabel label) {
        return label;
    }
}
