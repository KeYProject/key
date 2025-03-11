/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;

/**
 * The {@link TermLabelMerger} used to merge {@link FormulaTermLabel}s.
 *
 * @author Martin Hentschel
 */
public class FormulaTermLabelMerger implements TermLabelMerger {
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean mergeLabels(SequentFormula existingSF, Term existingTerm,
            TermLabel existingLabel, SequentFormula rejectedSF, Term rejectedTerm,
            TermLabel rejectedLabel, List<TermLabel> mergedLabels) {
        if (existingLabel != null) {
            FormulaTermLabel fExisting = (FormulaTermLabel) existingLabel;
            FormulaTermLabel fRejected = (FormulaTermLabel) rejectedLabel;
            // Compute new label
            List<String> newBeforeIds = new ArrayList<>(Arrays.asList(fExisting.getBeforeIds()));
            newBeforeIds.add(fRejected.getId());
            newBeforeIds.addAll(Arrays.asList(fRejected.getBeforeIds()));
            FormulaTermLabel newLabel =
                new FormulaTermLabel(fExisting.getMajorId(), fExisting.getMinorId(), newBeforeIds);
            // Remove existing label
            mergedLabels.remove(existingLabel);
            // Add new label
            mergedLabels.add(newLabel);
        } else {
            mergedLabels.add(rejectedLabel);
        }
        return true;
    }
}
