package org.key_project.proofmanagement.check;

import java.nio.file.Path;
import java.util.List;

public interface Checker {
    /**
     * Checks the given proof files for consistency.
     * @param proofFiles the paths of the *.proof files to check
     * @param data previous checkers may share data via this parameter
     * @return the result and messages of the checker wrapped in CheckResult
     */
    public CheckerData check(List<Path> proofFiles, CheckerData data);
}
