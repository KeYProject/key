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
        super("Multiple errors occured");
        this.errors = errors;
    }

    public List<BuildingIssue> getErrors() {
        return errors;
    }
}
