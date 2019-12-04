package de.uka.ilkd.key.nparser;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (12/4/19)
 */
public class BuildingExceptions extends RuntimeException {
    private final List<BuildingException> errors;

    public BuildingExceptions(List<BuildingException> errors) {
        super("Multiple errors occured");
        this.errors = errors;
    }

    public List<BuildingException> getErrors() {
        return errors;
    }
}
