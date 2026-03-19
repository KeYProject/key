/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

import org.key_project.proofmanagement.io.ProofBundleHandler;

/**
 * A checker for a proof related property.
 *
 * @author Wolfram Pfeifer
 */
public interface Checker {
    /**
     * Checks the given proof bundle for consistency.
     *
     * @param pbh the ProofBundleHandler to access the bundle
     * @param data container to share data between checkers and to store results
     * @throws ProofManagementException if the ProofManagement has to be aborted
     *         due to a critical error
     */
    void check(ProofBundleHandler pbh, CheckerData data) throws ProofManagementException;
}
