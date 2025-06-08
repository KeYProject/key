/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;
import org.key_project.util.collection.ImmutableList;

/// The `ProverCore` interface defines the core operations for managing
/// and executing automated proof strategies in the KeY framework. Implementations
/// of this interface provide mechanisms to start proof searches, manage listeners
/// for proof tasks, and handle interruption or resource cleanup.
///
/// @param
/// The type of proof object, which extends [ProofObject].
/// @param <G> The type of proof goal, which extends [ProofGoal].
public interface ProverCore<P extends ProofObject<G>, G extends ProofGoal<G>> {

    /// A constant used by some listeners to identify that a proof macro is running.
    String PROCESSING_STRATEGY = "Processing Strategy";

    /// Starts a proof search for the given goal using the specified proof instance and
    /// the strategy settings provided by the proof instance.
    ///
    /// @param proof The [ProofObject] representing the proof instance.
    /// @param goal The [ProofGoal] to prove.
    /// @return An [ProofSearchInformation] object containing information about the performed
    /// work,
    /// such as the number of rules applied.
    ProofSearchInformation<P, G> start(P proof, G goal);

    /// Starts a proof search for a list of goals using the specified proof instance and
    /// strategy settings provided by the proof instance.
    ///
    /// @param proof The [ProofObject] representing the proof instance.
    /// @param goals An [ImmutableList] of [ProofGoal] objects to prove.
    /// @return An [ProofSearchInformation] object containing information about the performed
    /// work,
    /// such as the number of rules applied.
    ProofSearchInformation<P, G> start(P proof, ImmutableList<G> goals);

    /// Starts a proof search for a list of goals using the specified proof instance and
    /// the provided strategy settings.
    ///
    /// @param proof The [ProofObject] representing the proof instance.
    /// @param goals An [ImmutableList] of [ProofGoal] objects to prove.
    /// @param stratSet The strategy settings to use during the proof search.
    /// @return An [ProofSearchInformation] object containing information about the performed
    /// work,
    /// such as the number of rules applied.
    ProofSearchInformation<P, G> start(P proof, ImmutableList<G> goals, Object stratSet);

    /// Starts a proof search for a list of goals using the specified proof instance,
    /// with configurable options for maximum steps, timeout, and early termination.
    ///
    /// @param proof The [ProofObject] representing the proof instance.
    /// @param goals An [ImmutableList] of [ProofGoal] objects to prove.
    /// @param maxSteps The maximum number of rule applications to perform.
    /// @param timeout The maximum duration (in milliseconds) to perform the proof search.
    /// @param stopAtFirstNonCloseableGoal If `true`, the proof search stops at the
    /// first encountered non-closeable goal.
    /// @return An [ProofSearchInformation] object containing information about the performed
    /// work,
    /// such as the number of rules applied.
    ProofSearchInformation<P, G> start(P proof, ImmutableList<G> goals, int maxSteps, long timeout,
            boolean stopAtFirstNonCloseableGoal);

    /// Adds a listener to monitor proof task events.
    ///
    /// @param observer The [ProverTaskListener] to add.
    void addProverTaskObserver(ProverTaskListener observer);

    /// Removes a listener that monitors proof task events.
    ///
    /// @param observer The [ProverTaskListener] to remove.
    void removeProverTaskObserver(ProverTaskListener observer);

    /// Clears all resources and state associated with the current proof session.
    /// This is typically called when a proof obligation is abandoned to prevent
    /// memory leaks and ensure that references to the proof are reset.
    void clear();

    /// Indicates whether the last proof run was interrupted due to an [InterruptedException].
    /// This flag allows detection of interruptions even when the exception has been swallowed
    /// by the system.
    ///
    /// @return `true` if the last run was interrupted, `false` otherwise.
    boolean hasBeenInterrupted();

}
