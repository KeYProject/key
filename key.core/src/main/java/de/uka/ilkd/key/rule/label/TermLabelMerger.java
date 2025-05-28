/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;

import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

/**
 * <p>
 * A {@link TermLabelMerger} is used by
 * {@link TermLabelManager#mergeLabels(Services, de.uka.ilkd.key.logic.SequentChangeInfo)} to merge
 * {@link TermLabel}s in case a {@link SequentFormula} was rejected to be added to the resulting
 * {@link Sequent}.
 * </p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained during prove read the
 * documentation of interface {@link TermLabel}.
 * </p>
 *
 * @author Martin Hentschel
 * @see TermLabel
 * @see TermLabelManager
 */
public interface TermLabelMerger {
    /**
     * Merges the existing and the rejected {@link TermLabel} by updating the merged {@link List}.
     *
     * @param existingSF The existing {@link SequentFormula}.
     * @param existingTerm The {@link JTerm} of the existing {@link SequentFormula}.
     * @param existingLabel The existing {@link TermLabel} if available or {@code null} otherwise.
     * @param rejectedSF The rejected {@link SequentFormula}.
     * @param rejectedTerm The {@link JTerm} of the rejected {@link SequentFormula}.
     * @param rejectedLabel The rejected {@link TermLabel}.
     * @param mergedLabels The {@link List} with new {@link TermLabel}s which will be visible in the
     *        resulting {@link Sequent}.
     * @return {@code true} if the {@link List} of {@link TermLabel} was modified and {@code false}
     *         otherwise.
     */
    boolean mergeLabels(SequentFormula existingSF, JTerm existingTerm,
            TermLabel existingLabel, SequentFormula rejectedSF,
            JTerm rejectedTerm,
            TermLabel rejectedLabel, List<TermLabel> mergedLabels);
}
