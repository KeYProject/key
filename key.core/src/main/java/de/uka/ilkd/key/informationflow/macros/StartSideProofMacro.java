/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Proof;

public interface StartSideProofMacro extends ProofMacro {
    /**
     * Key used in {@link ProofMacroFinishedInfo} to store the original {@link Proof}.
     */
    String PROOF_MACRO_FINISHED_INFO_KEY_ORIGINAL_PROOF = "originalProof";
}
