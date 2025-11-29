/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import org.key_project.prover.engine.TaskStartedInfo.TaskKind;

public record TaskStartedInfo(String message, int size, TaskKind kind)
        implements KeYDataTransferObject {
    public static TaskStartedInfo from(org.key_project.prover.engine.TaskStartedInfo info) {
        return new TaskStartedInfo(info.message(), info.size(), info.kind());
    }
}
