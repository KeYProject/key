/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.logic.Term;
import org.key_project.logic.op.sv.OperatorSV;
import org.key_project.util.collection.ImmutableList;

/**
 * Represents a trigger for applying a taclet in the KeY system.
 * A {@code Trigger} consists of a schema variable ({@code triggerVar}), a trigger term
 * {@code trigger}
 * that contains the {@code triggerVar} variable and
 * a list of formulas ({@code avoidConditions}) that should not be satisfied in
 * order to apply the taclet automatically.
 * <p>
 * A trigger is activated if the trigger term {@code trigger} can be matched against a formula/term
 * occurring in the
 * sequent and the such found instantiation for the trigger variable {@code triggerVar} does not
 * satisfy the
 * avoid conditions {@code avoidConditions}.
 * </p>
 *
 *
 * The {@code Trigger} is used to determine whether the application of a taclet is promising in a
 * given proof situation.
 * A {@code Trigger} has <strong>no</strong> influence on correctness of the rule, and in
 * particular, does not influence
 * the rule's applicability. The rule itself must be correct in any situation where it is
 * applicable.
 *
 */
public record Trigger(OperatorSV triggerVar, Term trigger, ImmutableList<Term> avoidConditions) {
    /**
     * Constructs a new {@code Trigger}.
     *
     * @param triggerVar the symbolic variable associated with the trigger. Must not be null.
     * @param trigger the condition that triggers the application of the taclet. Must not be null.
     * @param avoidConditions a list of conditions that must not be met in order to apply the
     *        taclet.
     *        If the list is empty, no avoid conditions are present. Must not be null.
     */
    public Trigger {
        assert triggerVar != null;
        assert trigger != null;
        assert avoidConditions != null;
    }

    /**
     * Checks whether there are any conditions to indicate to strategies that an application of the
     * taclet is not
     * promising in the current proof situation.
     *
     * @return {@code true} if there are avoid conditions, {@code false} otherwise.
     */
    public boolean hasAvoidConditions() { return !avoidConditions.isEmpty(); }
}
