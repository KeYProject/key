package org.key_project.proofmanagement.check;

import org.key_project.proofmanagement.check.CheckResult;
import org.key_project.proofmanagement.check.Checker;

import java.nio.file.Path;
import java.util.List;

/**
 * Checks that all files stored in the bundle can successfully be replayed.
 */
public class ReplayChecker implements Checker {
    @Override
    public CheckResult check(List<Path> proofFiles) {
        return null;
    }
}
