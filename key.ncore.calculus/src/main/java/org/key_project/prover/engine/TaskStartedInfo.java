/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

/**
 * Represents information about a prover task that is about to start.
 *
 * <p>
 * This interface is used to encapsulate details about a task, such as its type,
 * description, and estimated size. It can be used to provide
 * feedback about the task's progress, especially in graphical user interfaces.
 * </p>
 *
 * <h2>Features</h2>
 * <ul>
 * <li>Describes the type or "kind" of the task.</li>
 * <li>Provides a user-readable message describing the task.</li>
 * <li>Indicates the estimated size of the task for progress tracking.</li>
 * </ul>
 *
 */
public interface TaskStartedInfo {


    /**
     * Enumerates the kinds of tasks that can be represented.
     */
    enum TaskKind {
        /**
         * Represents tasks related to the proof search using strategies.
         */
        Strategy,

        /**
         * Represents tasks related to the proof search using proof macros.
         */
        Macro,

        /**
         * Represents tasks initiated by the user interface, such as user-triggered events.
         */
        UserInterface,

        /**
         * Represents tasks related to proof or problem loading
         */
        Loading,

        /**
         * Represents other miscellaneous tasks that do not fall into specific categories.
         */
        Other
    }

    /**
     * Retrieves the kind of the task.
     *
     * @return the kind of the task, as an instance of {@link TaskKind}.
     */
    TaskKind kind();

    /**
     * Retrieves a descriptive message about the task.
     *
     * <p>
     * This is typically a short, user-readable description of the task, such as
     * "Processing Strategy"
     * </p>
     *
     * @return a message describing the task.
     */
    String message();

    /**
     * Retrieves the estimated size of the task.
     *
     * <p>
     * This value indicates the amount of work needed to complete the task. It is primarily
     * used by graphical user interfaces to provide progress feedback (e.g., progress bars).
     * </p>
     *
     * <p>
     * A size of {@code 0} indicates that the size of the task is unknown.
     * </p>
     *
     * @return an integer representing the size of the task, or {@code 0} if the size is unknown.
     */
    int size();

}
