/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;

/**
 * The rule application for which term labels are computed or refactored. One instance is created
 * per {@link TermLabelManager} entry point invocation and passed unchanged to all term label
 * hooks ({@link de.uka.ilkd.key.rule.label.TermLabelPolicy},
 * {@link de.uka.ilkd.key.rule.label.TermLabelUpdate},
 * {@link de.uka.ilkd.key.rule.label.TermLabelRefactoring}); the hooks receive their varying
 * payload (the term being created or refactored, the label set) as separate parameters.
 *
 * @param state the {@link TermLabelState} of the current rule application (mutable scratchpad
 *        shared by all hook invocations of one rule application)
 * @param services the {@link Services} of the proof the rule is applied in
 * @param applicationPosInOccurrence the {@link PosInOccurrence} in the previous {@link Sequent}
 *        which defines the term that is rewritten, or {@code null} if not available (e.g. proof
 *        obligation creation)
 * @param applicationTerm the term defined by {@code applicationPosInOccurrence}, or {@code null}
 * @param modalityTerm the modality term below the updates of {@code applicationTerm}
 *        (see {@code TermBuilder.goBelowUpdates}), or {@code null} where it was not computed
 *        (refactoring entry points; no modality hooks registered)
 * @param rule the {@link Rule} which is applied, or {@code null}
 * @param ruleApp the {@link RuleApp} which is currently performed, or {@code null} where the
 *        entry point does not receive it (refactoring entry points)
 * @param goal the optional {@link Goal} on which the new or refactored term will be used, or
 *        {@code null}
 * @param hint an optional hint passed from the active rule to describe the term which should be
 *        created, or {@code null}
 * @param tacletTerm the taclet term which is responsible for the new term, or {@code null} in
 *        case of built-in rules
 */
public record TermLabelContext(
        TermLabelState state,
        Services services,
        PosInOccurrence applicationPosInOccurrence,
        JTerm applicationTerm,
        JTerm modalityTerm,
        Rule rule,
        RuleApp ruleApp,
        Goal goal,
        Object hint,
        JTerm tacletTerm) {
}
