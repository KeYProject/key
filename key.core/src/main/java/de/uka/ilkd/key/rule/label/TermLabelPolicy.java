/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.rules.Rule;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;


/**
 * <p>
 * A {@link TermLabelPolicy} is used by
 * {@link TermLabelManager#instantiateLabels}
 * to decide for each {@link TermLabel} of an old {@link JTerm} if it should be re-added to the new
 * {@link JTerm} or not.
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
public interface TermLabelPolicy {
    /**
     * Decides to keep (add to term which will be created) or to drop (do not add label to new term)
     * the given {@link TermLabel} provided by the application {@link JTerm}.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link JTerm} that is rewritten.
     * @param applicationTerm The {@link JTerm} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link JTerm} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link JTerm} in the taclet which is responsible to
     *        instantiate
     *        the new {@link JTerm} for the new proof node or {@code null} in case of built in
     *        rules.
     * @param newTerm the template for the new {@link JTerm} to create
     * @param label The {@link TermLabel} to decide if it should be kept or dropped.
     * @return The {@link TermLabel} to keep which might be a different one (e.g. with changed
     *         parameters) or {@code null} if the {@link TermLabel} should be dropped.
     */
    TermLabel keepLabel(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence,
            JTerm applicationTerm, Rule rule, Goal goal,
            Object hint, JTerm tacletTerm,
            JTerm newTerm, TermLabel label);
}
