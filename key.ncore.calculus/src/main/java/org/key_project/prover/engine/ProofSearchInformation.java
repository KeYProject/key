/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// Represents a contract for gathering and accessing information about the application
/// of a proof strategy during automated reasoning in the KeY system.
///
/// This interface is intended to provide key details about the execution of a proof strategy,
/// including:
///
/// - The reason for the strategy execution.
/// - The proof object and its associated state.
/// - Statistics such as the number of closed goals and applied rule applications.
/// - Details about unresolved goals or exceptions encountered during execution.
/// - The total time taken for the execution.
///
///
///
/// The `ApplyStrategyInfo` interface is generic and designed to work with specific
/// types of proof objects and proof goals. Implementations are expected to provide immutable
/// containers for these details, ensuring reliable reporting of strategy execution results.
///
///
/// This interface is typically used in conjunction with strategy execution workflows,
/// enabling higher-level tools or users to analyze and respond to proof results, including
/// resolving unresolved goals or handling errors.
///
///
/// @param
/// the type of the proof object, extending [ProofObject]
/// @param <G> the type of the proof goal, extending [ProofGoal]
///
/// @see org.key_project.prover.proof.ProofObject
/// @see org.key_project.prover.proof.ProofGoal
public interface ProofSearchInformation<P extends ProofObject<@NonNull G>, G extends ProofGoal<@NonNull G>> {

    /// Retrieves the explanation or reason wjy the proof search (strategy execution) finished.
    ///
    /// This message provides context for why the strategy terminated, and it can
    /// be used for logging or user feedback purposes. Possible reasons are for example (not
    /// exhaustive):
    /// proof could be closed, timeout, maximal number of rule applications reached or an exception
    /// was thrown.
    ///
    ///
    /// @return a string describing the reason for applying the strategy
    String reason();

    /// Returns the proof object associated with this strategy application.
    ///
    /// The proof object represents the state of the proof at the
    /// conclusion of the strategy execution.
    ///
    ///
    /// @return the proof object of type `P`
    P getProof();

    /// Retrieves one of non-closeable proof goals, if one exists.
    ///
    /// A non-closeable goal represents a proof goal that could not be resolved
    /// or closed by the applied strategy. This can occur when the automated reasoning
    /// process encounters conditions requiring external input or manual intervention.
    ///
    ///
    /// @return the unresolved goal of type `G`, or `null` if all goals were closed
    @Nullable
    G nonCloseableGoal();

    /// Indicates whether an error occurred during the strategy execution.
    ///
    /// An error might occur due to unexpected conditions, such as invalid inputs,
    /// unsupported proof configurations, or system failures during the reasoning process.
    ///
    ///
    /// @return `true` if an error occurred, otherwise `false`
    boolean isError();

    /// Retrieves the exception that occurred during strategy execution, if any.
    ///
    /// This method provides access to the specific [Throwable] encountered during
    /// the proof strategy application, which can be used for debugging or error handling purposes.
    ///
    ///
    /// @return the exception encountered during execution, or `null` if no error occurred
    Throwable getException();

    /// Returns the total time taken for the strategy application, in milliseconds.
    ///
    /// This metric allows for performance evaluation and optimization of proof strategies.
    ///
    ///
    /// @return the execution time in milliseconds
    long getTime();

    /// Retrieves the number of proof goals that were successfully closed during the strategy
    /// execution.
    ///
    /// A closed goal is one that was fully resolved and requires no further reasoning.
    ///
    ///
    /// @return the number of closed goals
    int getNumberOfClosedGoals();

    /// Retrieves the number of rule applications performed during the strategy execution.
    ///
    /// This statistic provides insight into the complexity and effort involved in resolving the
    /// proof.
    ///
    ///
    /// @return the number of rule applications performed
    int getNumberOfAppliedRuleApps();

}
