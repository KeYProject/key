/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.parsing;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (12/4/19)
 */
public class BuildingExceptions extends RuntimeException {
    private final List<BuildingIssue> errors;

    public BuildingExceptions(List<BuildingIssue> errors) {
        super(formatMessage(errors));
        this.errors = errors;
    }

    private static String formatMessage(List<BuildingIssue> errors) {
        var sb = new StringBuilder();
        sb.append("Multiple errors occurred:");
        for (BuildingIssue error : errors) {
            sb.append(System.lineSeparator())
                    .append(error.position())
                    .append(": ")
                    .append(error.message());
        }

        return sb.toString();
    }

    public List<BuildingIssue> getErrors() {
        return errors;
    }
}
