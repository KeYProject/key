package org.key_project.proofmanagement.check;

import java.nio.file.Path;
import java.util.List;

/**
 * Checks that there exists a proof for every contract.
 * Has to be combined with other checkers to ensure that the proofs are actually consistent
 * as well as correct.
 */
public class MissingProofsChecker implements Checker {
    @Override
    public CheckResult check(List<Path> proofFiles) {
        return null;
    }
}
