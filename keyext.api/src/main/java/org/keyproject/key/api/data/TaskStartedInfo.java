/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

public record TaskStartedInfo() implements KeYDataTransferObject {
    public static TaskStartedInfo from(de.uka.ilkd.key.prover.TaskStartedInfo info) {
        return new TaskStartedInfo();
    }
}
