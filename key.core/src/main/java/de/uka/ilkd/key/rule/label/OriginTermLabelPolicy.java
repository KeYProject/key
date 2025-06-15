/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.Rule;
import org.key_project.prover.sequent.PosInOccurrence;

/**
 * Policy for {@link OriginTermLabel}s.
 *
 * This ensures that every term always has a valid term label, i.e., that no labels are lost.
 *
 * @author lanzinger
 */
public class OriginTermLabelPolicy implements TermLabelPolicy {

    @Override
    public TermLabel keepLabel(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, JTerm applicationTerm, Rule rule, Goal goal,
            Object hint, JTerm tacletTerm,
            JTerm newTerm, TermLabel label) {
        if (services.getProof() == null) {
            return label;
        }

        if (services.getTermBuilder().getOriginFactory() == null) {
            return null;
        }

        if (!OriginTermLabel.canAddLabel(newTerm.op(), services)) {
            return null;
        }

        OriginTermLabel newLabel = (OriginTermLabel) label;
        OriginTermLabel oldLabel = null;

        for (TermLabel l : newTerm.getLabels()) {
            if (l instanceof OriginTermLabel && l != newLabel) {
                oldLabel = (OriginTermLabel) l;
                break;
            }
        }

        OriginTermLabel result;

        if (oldLabel == null) {
            result = newLabel;
        } else {
            result = oldLabel;
        }

        if (result.getOrigin().specType == SpecType.NONE && result.getSubtermOrigins().isEmpty()) {
            result = null;
        }

        return result;
    }
}
