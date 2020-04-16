package org.key_project.proofmanagement.check;

import java.nio.file.Path;
import java.util.List;

/**
 * Checks that all files stored in the bundle can successfully be replayed.
 *
 * @author Wolfram Pfeifer
 */
public class ReplayChecker implements Checker {

    @Override
    public void check(List<Path> proofFiles, CheckerData data) throws ProofManagementException {
        data.addCheck("replay");
        data.print("Running replay checker ...");
        ProverService.ensureProofsReplayed(proofFiles, data);
    }
}
