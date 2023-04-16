package de.uka.ilkd.key.java;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (16.04.23)
 */
public class JavaBuildingExceptions extends RuntimeException {
    private final List<JavaBuildingIssue> issues;

    public JavaBuildingExceptions(List<JavaBuildingIssue> issues) {
        this.issues = issues;
    }

    public List<JavaBuildingIssue> getIssues() {
        return issues;
    }
}
