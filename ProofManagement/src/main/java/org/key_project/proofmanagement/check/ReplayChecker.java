package org.key_project.proofmanagement.check;

import java.nio.file.Path;
import java.util.List;

/**
 * Checks that all files stored in the bundle can successfully be replayed.
 */
public class ReplayChecker implements Checker {
    @Override
    public CheckerData check(List<Path> proofFiles, CheckerData currentRes) {
        return null;
    }
}
