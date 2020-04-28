package org.key_project.proofmanagement.check;

import org.key_project.proofmanagement.io.ProofBundleHandler;

/**
 * Checks that all files stored in the bundle can successfully be replayed.
 *
 * @author Wolfram Pfeifer
 */
public class ReplayChecker implements Checker {

    @Override
    public void check(ProofBundleHandler pbh, CheckerData data) throws ProofManagementException {
        data.addCheck("replay");
        data.print("Running replay checker ...");
        KeYFassade.ensureProofsReplayed(data);
    }
}
