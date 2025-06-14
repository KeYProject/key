/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

/// Listener for longer tasks, which may be run in a separate worker thread. Examples: proof
/// loading,
/// processing strategies
public interface ProverTaskListener {
    /// Called when a task is about to start.
    ///
    /// @param info a TaskStartedInfo object with information about the task
    void taskStarted(TaskStartedInfo info);

    /// Called when progress is made on a task.
    ///
    /// This method is called after every single step of the task
    ///
    ///
    /// @param position indicates how much work has been done relative to the value of `size`
    /// passed in [#taskStarted(TaskStartedInfo)].
    void taskProgress(int position);


    /// Called when a task is finished.
    ///
    /// @param info a TaskFinishedInfo object with additional information
    void taskFinished(TaskFinishedInfo info);
}
