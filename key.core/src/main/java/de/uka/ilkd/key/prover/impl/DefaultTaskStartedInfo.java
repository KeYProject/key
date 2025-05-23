/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.prover.TaskStartedInfo;

/**
 * Default implementation of a {@link TaskStartedInfo}.
 */
public record DefaultTaskStartedInfo(TaskKind kind, String message, int size)
        implements TaskStartedInfo {
    /**
     * {@inheritDoc}
     */
    @Override
    public TaskKind kind() {
        return kind;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String message() {
        return message;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int size() {
        return size;
    }
}
