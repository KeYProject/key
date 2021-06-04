package de.uka.ilkd.key.nparser;

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
