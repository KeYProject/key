/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * <p>
 * A {@link ChildTermLabelPolicy} is used by
 * {@link TermLabelManager#instantiateLabels(TermLabelState, Services, PosInOccurrence, Rule, RuleApp, Goal, Object, Term, Term)}
 * to decide for each {@link TermLabel} on a child or grandchild of the application {@link Term} if
 * it should be re-added to the new {@link Term} or not.
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
public interface ChildTermLabelPolicy extends RuleSpecificTask {
    /**
     * Decides if the currently active {@link Rule} application is supported or not. If it is not
     * supported no iteration over children will be executed. Only if it returns {@code true}
     * {@link #addLabel( TermServices, PosInOccurrence, Term, Rule, Goal, Object, Term, Term, Term, TermLabel)}
     * will
     * be called if a child {@link Term} contains a managed label.
     *
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @return {@code true} keep {@link TermLabel} and add it to the new {@link Term}. {@code false}
     *         drop {@link TermLabel} and do not need it to the new {@link Term}.
     */
    boolean isRuleApplicationSupported(TermServices services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term newTerm);

    /**
     * <p>
     * Decides to add or not to add the given {@link TermLabel} on a child or grandchild of the
     * application {@link Term} to the new {@link Term} which will be created.
     * </p>
     * <p>
     * If the child {@link Term} is still a child of the new {@link Term} the label will still exist
     * independent from the result of this method on the child. To remove it from the child a
     * refacotring has to be used instead.
     * </p>
     *
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @param childTerm The {@link Term} which is a child or grandchild of the application
     *        {@link Term} that provides the {@link TermLabel}.
     * @param label The {@link TermLabel} to decide if it should be kept or dropped.
     * @return {@code true} add {@link TermLabel} to new {@link Term}. {@code false} do not add
     *         {@link TermLabel} to new {@link Term}.
     */
    boolean addLabel(TermServices services, PosInOccurrence applicationPosInOccurrence,
            Term applicationTerm, Rule rule, Goal goal, Object hint, Term tacletTerm,
            Term newTerm, Term childTerm, TermLabel label);
}
