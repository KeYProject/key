/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;

import org.jspecify.annotations.NonNull;

/// Represents information about the result of a single rule application in the KeY verification
/// system.
///
/// This class encapsulates whether a rule was applied successfully or not, along with
/// relevant details such as the reason for failure (if applicable), the associated proof goal,
/// and the applied rule. It is used in the context of symbolic execution and proof obligations
/// to track the outcome of applying a specific rule.
///
///
/// Instances of this class are created to indicate the result of a rule application:
///
///
/// - If the rule application is successful, a success message and the applied rule are
/// stored.
/// - If the rule application fails, an explanatory message and relevant details are stored.
///
///
/// @see org.key_project.prover.proof.ProofGoal
/// @see RuleApp
public class SingleRuleApplicationInfo {

    /// Indicates whether the rule was applied successfully.
    private final boolean success;

    /// Stores a message explaining the result of the rule application.
    /// This could be a success message or a reason for failure.
    private final String message;
    /// The proof goal associated with the rule application.
    private final ProofGoal<?> goal;
    /// The rule that was applied.
    private final RuleApp appliedRuleApp;

    /// Constructs a new `SingleRuleApplicationInfo` for a successful rule application.
    ///
    /// @param mayCloseableGoal the proof goal that may be closed by this rule application.
    /// @param appliedRuleApp the rule that was successfully applied.
    public SingleRuleApplicationInfo(ProofGoal<?> mayCloseableGoal,
            RuleApp appliedRuleApp) {
        this.message = "Rule applied successful";
        this.goal = mayCloseableGoal;
        this.appliedRuleApp = appliedRuleApp;
        this.success = true;
    }

    /// Constructs a new `SingleRuleApplicationInfo` for a failed rule application.
    ///
    /// @param message a message explaining why the rule application failed.
    /// @param nonCloseableGoal the proof goal that could not be closed by this rule application.
    /// @param appliedRuleApp the rule that was applied (if any).
    public SingleRuleApplicationInfo(String message, ProofGoal<?> nonCloseableGoal,
            RuleApp appliedRuleApp) {
        this.message = message;
        this.goal = nonCloseableGoal;
        this.appliedRuleApp = appliedRuleApp;
        this.success = false;
    }

    /// Checks whether the rule application was successful.
    ///
    /// @return `true` if the rule application was successful, `false` otherwise.
    public boolean isSuccess() {
        return success;
    }

    /// Retrieves the proof goal associated with this rule application.
    ///
    /// @param <G> the type of the proof goal.
    /// @return the proof goal associated with this rule application.
    public <G extends ProofGoal<@NonNull G>> G getGoal() {
        // noinspection unchecked
        return (G) goal;
    }

    /// Retrieves the message explaining the result of the rule application.
    ///
    /// For successful applications, this will typically be a success message.
    /// For unsuccessful applications, it will explain why the rule could not be applied.
    ///
    ///
    /// @return the result message of the rule application.
    public String message() {
        return message;
    }

    /// Retrieves the rule that was applied.
    ///
    /// @return the applied rule, or `null` if no rule was applied.
    public RuleApp getAppliedRuleApp() {
        return appliedRuleApp;
    }
}
