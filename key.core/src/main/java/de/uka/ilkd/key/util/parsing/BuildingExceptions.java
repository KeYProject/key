/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.parsing;

import java.util.List;

import org.key_project.util.parsing.HasLocation;
import org.key_project.util.parsing.Location;

import org.jspecify.annotations.NonNull;

/**
 * An exception that bundles several {@link BuildingIssue}s that occurred while building KeY
 * structures (e.g., while parsing Java compilation units via the JavaParser).
 *
 * @author Alexander Weigl
 * @version 1 (12/4/19)
 */
public class BuildingExceptions extends RuntimeException implements HasLocation {
    private final List<BuildingIssue> errors;

    public BuildingExceptions(List<BuildingIssue> errors) {
        super(formatMessage(errors));
        this.errors = errors;
    }

    private static String formatMessage(List<BuildingIssue> errors) {
        var sb = new StringBuilder();
        // Be precise about how many problems there are; "Multiple errors" is misleading
        // when there is in fact only a single problem to report.
        if (errors.size() == 1) {
            sb.append("Error occurred:");
        } else {
            sb.append(errors.size()).append(" errors occurred:");
        }
        for (BuildingIssue error : errors) {
            sb.append(System.lineSeparator());
            if (error.sourceName() != null) {
                sb.append(error.sourceName()).append(":");
            }
            sb.append(error.position())
                    .append(": ")
                    .append(error.message());
        }

        return sb.toString();
    }

    public List<BuildingIssue> getErrors() {
        return errors;
    }

    /**
     * Returns the location of the first reported issue (if any) so that tooling and the
     * {@code ExceptionTools} can point the user to the origin of the problem. Previously this
     * exception carried no location at all, so the position information stored in the individual
     * {@link BuildingIssue}s was lost.
     */
    @Override
    public @NonNull Location getLocation() {
        for (BuildingIssue issue : errors) {
            if (issue.position() != null) {
                return issue.getLocation();
            }
        }
        return Location.UNDEFINED;
    }
}
