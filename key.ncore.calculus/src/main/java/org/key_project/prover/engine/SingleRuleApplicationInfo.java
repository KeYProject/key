/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;

/**
 * Represents information about the result of a single rule application in the KeY verification
 * system.
 *
 * <p>
 * This class encapsulates whether a rule was applied successfully or not, along with
 * relevant details such as the reason for failure (if applicable), the associated proof goal,
 * and the applied rule. It is used in the context of symbolic execution and proof obligations
 * to track the outcome of applying a specific rule.
 * </p>
 *
 * <p>
 * Instances of this class are created to indicate the result of a rule application:
 * </p>
 * <ul>
 * <li>If the rule application is successful, a success message and the applied rule are
 * stored.</li>
 * <li>If the rule application fails, an explanatory message and relevant details are stored.</li>
 * </ul>
 *
 *
 * @see org.key_project.prover.proof.ProofGoal
 * @see org.key_project.prover.rules.RuleApp
 */
public class SingleRuleApplicationInfo {

    /**
     * Indicates whether the rule was applied successfully.
     */
    private final boolean success;

    /**
     * Stores a message explaining the result of the rule application.
     * This could be a success message or a reason for failure.
     */
    private final String message;
    /**
     * The proof goal associated with the rule application.
     */
    private final ProofGoal<?> goal;
    /**
     * The rule that was applied.
     */
    private final RuleApp appliedRuleApp;

    /**
     * Constructs a new {@code SingleRuleApplicationInfo} for a successful rule application.
     *
     * @param mayCloseableGoal the proof goal that may be closed by this rule application.
     * @param appliedRuleApp the rule that was successfully applied.
     */
    public SingleRuleApplicationInfo(ProofGoal<?> mayCloseableGoal,
            RuleApp appliedRuleApp) {
        this.message = "Rule applied successful";
        this.goal = mayCloseableGoal;
        this.appliedRuleApp = appliedRuleApp;
        this.success = true;
    }

    /**
     * Constructs a new {@code SingleRuleApplicationInfo} for a failed rule application.
     *
     * @param message a message explaining why the rule application failed.
     * @param nonCloseableGoal the proof goal that could not be closed by this rule application.
     * @param appliedRuleApp the rule that was applied (if any).
     */
    public SingleRuleApplicationInfo(String message, ProofGoal<?> nonCloseableGoal,
            RuleApp appliedRuleApp) {
        this.message = message;
        this.goal = nonCloseableGoal;
        this.appliedRuleApp = appliedRuleApp;
        this.success = false;
    }

    /**
     * Checks whether the rule application was successful.
     *
     * @return {@code true} if the rule application was successful, {@code false} otherwise.
     */
    public boolean isSuccess() {
        return success;
    }

    /**
     * Retrieves the proof goal associated with this rule application.
     *
     * @param <G> the type of the proof goal.
     * @return the proof goal associated with this rule application.
     */
    public <G extends ProofGoal<G>> G getGoal() {
        return (G) goal;
    }

    /**
     * Retrieves the message explaining the result of the rule application.
     *
     * <p>
     * For successful applications, this will typically be a success message.
     * For unsuccessful applications, it will explain why the rule could not be applied.
     * </p>
     *
     * @return the result message of the rule application.
     */
    public String message() {
        return message;
    }

    /**
     * Retrieves the rule that was applied.
     *
     * @return the applied rule, or {@code null} if no rule was applied.
     */
    public RuleApp getAppliedRuleApp() {
        return appliedRuleApp;
    }
}
