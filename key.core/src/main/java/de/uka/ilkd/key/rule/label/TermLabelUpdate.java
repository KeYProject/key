/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;


/**
 * <p>
 * A {@link TermLabelUpdate} is used by
 * {@link TermLabelManager#instantiateLabels(TermLabelState, Services, PosInOccurrence, JTerm, Rule, RuleApp, Goal, Object, JTerm, JTerm)}
 * to add or remove maintained {@link TermLabel}s which will be added to the new {@link JTerm}.
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
public interface TermLabelUpdate extends RuleSpecificTask {
    /**
     * This method can freely add, remove or sort the given {@link TermLabel} which will be added to
     * the new {@link JTerm}.
     *
     * @param state The {@link TermLabelState} of the current rule application. return {@code true}
     *        keep {@link TermLabel} and add it to the new {@link JTerm}. {@code false} drop
     *        {@link TermLabel} and do not need it to the new {@link JTerm}.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link JTerm} that is rewritten.
     * @param applicationTerm The {@link JTerm} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param modalityTerm The optional modality {@link JTerm}.
     * @param rule The {@link Rule} which is applied.
     * @param ruleApp The {@link RuleApp} which is currently performed.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link JTerm} in the taclet which is responsible to
     *        instantiate
     *        the new {@link JTerm} for the new proof node or {@code null} in case of built in
     *        rules.
     * @param newTerm the template for the new {@link JTerm} to create
     * @param labels The {@link Set} of {@link TermLabel}s to modify.
     */
    void updateLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence,
            JTerm applicationTerm, JTerm modalityTerm,
            Rule rule, RuleApp ruleApp, Object hint, JTerm tacletTerm,
            JTerm newTerm,
            Set<TermLabel> labels);
}
