/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofObject;

/// An interface that provides information about a task that has finished execution.
/// This includes various details such as the source of the task, its result, execution time,
/// the number of applied rules, the number of closed goals, and any associated proof.
///
/// Implementations of this interface are used to capture and provide detailed metrics
/// about completed tasks, which may be related to proof strategies, goal solving, or
/// proof verification.
///
public interface TaskFinishedInfo {

    /// Retrieves the source object of the finished task. The source could be any object
    /// that initiated or is associated with the task, such as a proof macro, a strategy
    /// applied, or a proof loader.
    ///
    /// @return The source object associated with the task.
    Object getSource();

    /// Retrieves the result of the task. This result may represent the outcome of the
    /// task execution, such as an exception (e.g., a [Throwable]), success status,
    /// or specific information about the strategy or proof.
    ///
    /// @return The result of the task, which could vary depending on the task's nature.
    Object getResult();

    /// Retrieves the total time spent to complete the task, measured in milliseconds.
    /// This provides insight into the task's performance and time consumption.
    ///
    /// @return The time taken by the task to finish, in milliseconds.
    long getTime();

    /// Retrieves the number of rules that were applied during the task execution.
    ///
    /// @return The number of applied rules.
    int getAppliedRules();

    /// Retrieves the number of goals that were closed during the task execution.
    ///
    /// @return The number of goals that were closed during the task.
    int getClosedGoals();

    /// Retrieves the proof associated with the task.
    ///
    /// @return The proof object related to the task.
    ProofObject<?> getProof();

}
