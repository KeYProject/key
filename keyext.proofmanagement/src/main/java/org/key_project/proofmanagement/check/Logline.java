/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.proofmanagement.check;

import org.key_project.proofmanagement.io.LogLevel;

/**
 * A record representing a line in the output log.
 *
 * @param level the {@link LogLevel} of the line
 * @param message the content
 */
public record Logline(LogLevel level, String message) {
    @Override
    public String toString() {
        return level + message;
    }
}
