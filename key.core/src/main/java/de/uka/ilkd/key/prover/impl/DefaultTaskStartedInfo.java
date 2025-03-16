/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import org.key_project.prover.engine.TaskStartedInfo;

/**
 * Default implementation of the {@link TaskStartedInfo} interface.
 *
 * <p>
 * This implementation is a record that provides an immutable representation of
 * task-related information. It includes the type of task, a descriptive message, and its
 * estimated size.
 * </p>
 *
 * @param kind the kind of the task, as defined in {@link TaskKind}.
 * @param message a user-readable description of the task.
 * @param size the estimated size of the task, or {@code 0} if unknown.
 * @see TaskStartedInfo
 * @see TaskStartedInfo.TaskKind
 */
public record DefaultTaskStartedInfo(TaskKind kind, String message, int size)
        implements TaskStartedInfo {
    /**
     * {@inheritDoc}
     */
    @Override
    public TaskKind kind() { return kind; }

    /**
     * {@inheritDoc}
     */
    @Override
    public String message() { return message; }

    /**
     * {@inheritDoc}
     */
    @Override
    public int size() { return size; }
}
