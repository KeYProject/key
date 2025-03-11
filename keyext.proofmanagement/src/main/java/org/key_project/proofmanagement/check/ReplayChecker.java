/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
        KeYFacade.ensureProofsReplayed(data);
    }
}
