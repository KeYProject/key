/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Represents a contract for gathering and accessing information about the application
 * of a proof strategy during automated reasoning in the KeY system.
 *
 * <p>
 * This interface is intended to provide key details about the execution of a proof strategy,
 * including:
 * <ul>
 * <li>The reason for the strategy execution.</li>
 * <li>The proof object and its associated state.</li>
 * <li>Statistics such as the number of closed goals and applied rule applications.</li>
 * <li>Details about unresolved goals or exceptions encountered during execution.</li>
 * <li>The total time taken for the execution.</li>
 * </ul>
 * </p>
 *
 * <p>
 * The {@code ApplyStrategyInfo} interface is generic and designed to work with specific
 * types of proof objects and proof goals. Implementations are expected to provide immutable
 * containers for these details, ensuring reliable reporting of strategy execution results.
 * </p>
 *
 * <p>
 * This interface is typically used in conjunction with strategy execution workflows,
 * enabling higher-level tools or users to analyze and respond to proof results, including
 * resolving unresolved goals or handling errors.
 * </p>
 *
 * @param <P> the type of the proof object, extending {@link ProofObject}
 * @param <G> the type of the proof goal, extending {@link ProofGoal}
 *
 * @see org.key_project.prover.proof.ProofObject
 * @see org.key_project.prover.proof.ProofGoal
 */
public interface ProofSearchInformation<P extends ProofObject<@NonNull G>, G extends ProofGoal<@NonNull G>> {

    /**
     * Retrieves the explanation or reason wjy the proof search (strategy execution) finished.
     *
     * <p>
     * This message provides context for why the strategy terminated, and it can
     * be used for logging or user feedback purposes. Possible reasons are for example (not
     * exhaustive):
     * proof could be closed, timeout, maximal number of rule applications reached or an exception
     * was thrown.
     * </p>
     *
     * @return a string describing the reason for applying the strategy
     */
    String reason();

    /**
     * Returns the proof object associated with this strategy application.
     *
     * <p>
     * The proof object represents the state of the proof at the
     * conclusion of the strategy execution.
     * </p>
     *
     * @return the proof object of type {@code P}
     */
    P getProof();

    /**
     * Retrieves one of non-closeable proof goals, if one exists.
     *
     * <p>
     * A non-closeable goal represents a proof goal that could not be resolved
     * or closed by the applied strategy. This can occur when the automated reasoning
     * process encounters conditions requiring external input or manual intervention.
     * </p>
     *
     * @return the unresolved goal of type {@code G}, or {@code null} if all goals were closed
     */
    @Nullable
    G nonCloseableGoal();

    /**
     * Indicates whether an error occurred during the strategy execution.
     *
     * <p>
     * An error might occur due to unexpected conditions, such as invalid inputs,
     * unsupported proof configurations, or system failures during the reasoning process.
     * </p>
     *
     * @return {@code true} if an error occurred, otherwise {@code false}
     */
    boolean isError();

    /**
     * Retrieves the exception that occurred during strategy execution, if any.
     *
     * <p>
     * This method provides access to the specific {@link Throwable} encountered during
     * the proof strategy application, which can be used for debugging or error handling purposes.
     * </p>
     *
     * @return the exception encountered during execution, or {@code null} if no error occurred
     */
    Throwable getException();

    /**
     * Returns the total time taken for the strategy application, in milliseconds.
     *
     * <p>
     * This metric allows for performance evaluation and optimization of proof strategies.
     * </p>
     *
     * @return the execution time in milliseconds
     */
    long getTime();

    /**
     * Retrieves the number of proof goals that were successfully closed during the strategy
     * execution.
     *
     * <p>
     * A closed goal is one that was fully resolved and requires no further reasoning.
     * </p>
     *
     * @return the number of closed goals
     */
    int getNumberOfClosedGoals();

    /**
     * Retrieves the number of rule applications performed during the strategy execution.
     *
     * <p>
     * This statistic provides insight into the complexity and effort involved in resolving the
     * proof.
     * </p>
     *
     * @return the number of rule applications performed
     */
    int getNumberOfAppliedRuleApps();

}
