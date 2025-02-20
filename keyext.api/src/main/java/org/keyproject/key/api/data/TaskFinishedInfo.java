/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

public record TaskFinishedInfo() {
    public static TaskFinishedInfo from(de.uka.ilkd.key.prover.TaskFinishedInfo info) {
        return new TaskFinishedInfo();
    }
}
