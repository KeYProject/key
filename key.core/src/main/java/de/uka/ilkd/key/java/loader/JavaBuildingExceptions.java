/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.loader;

import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (16.04.23)
 */
public class JavaBuildingExceptions extends RuntimeException {
    private final List<JavaBuildingIssue> issues;

    public JavaBuildingExceptions(List<JavaBuildingIssue> issues) {
        super(createMessage(issues));
        this.issues = issues;
    }

    private static String createMessage(List<JavaBuildingIssue> issues) {
        return issues.stream().map(JavaBuildingIssue::toString).collect(Collectors.joining("\n"));
    }

    public List<JavaBuildingIssue> getIssues() {
        return issues;
    }

    @Override
    public String toString() {
        return "JavaBuildingExceptions{" +
            "issues=" + issues +
            '}';
    }
}
