package org.key_project.proofmanagement.check;

import java.nio.file.Path;
import java.util.List;

/**
 * A checker for a proof related property. Input are Path objects to *.proof files and a container
 * object for storing intermediate data as well as check results.
 *
 * @author Wolfram Pfeifer
 */
public interface Checker {
    /**
     * Checks the given proof files for consistency.
     * @param proofFiles the paths of the *.proof files to check
     * @param data container to share data between checkers and to store results
     * @throws ProofManagementException if the ProofManagement has to be aborted
     *      due to a critical error
     */
    void check(List<Path> proofFiles, CheckerData data) throws ProofManagementException;
}
