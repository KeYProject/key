/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.io.File;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

/**
 * These tests check that the integer taclet options still work as intended, for example that the
 * additional branches for overflow checks are still generated correctly. At the moment, for each of
 * the three taclet options there is one positive (provable) and one negative (unprovable) test.
 *
 * @author Wolfram Pfeifer
 */
class IntSemanticsTest {
    private static final File TEST_DIR = new File(FindResources.getTestResourcesDirectory(),
        "/de/uka/ilkd/key/rule/intSemantics/");

    /**
     * This test checks that certain proofs containing integer corner cases are reloadable.
     *
     * @param filename name of the .proof file containing a closed proof and also setting the
     *        desired taclet option for the integer semantics.
     * @throws ProblemLoaderException should not happen
     */
    @ParameterizedTest
    @ValueSource(strings = { "java/mJava.proof",
        "uncheckedOF/mBigint.proof",
        "checkedOF/mOFCheck.proof" })
    void testSemanticsProvable(String filename) throws ProblemLoaderException {
        File proofFile = new File(TEST_DIR, filename);
        ProofManagementApi pmapi = KeYApi.loadProof(proofFile);
        Proof proof = pmapi.getLoadedProof().getProof();
        // Proof should be reloaded completely now. If not, the int semantics are probably broken.
        Assertions.assertTrue(proof.closed());
    }

    /**
     * This test checks that certain contracts are not provable with the selected integer semantics.
     *
     * @param filename name of the .key file that points to the contract. The desired integer
     *        semantics need to be set correctly here!
     * @throws ProblemLoaderException should not happen
     */
    @ParameterizedTest
    @ValueSource(strings = { "java/mJavaWrong.key",
        "uncheckedOF/mBigintWrong.key",
        "checkedOF/mOFCheckWrong.key", })
    void testSemanticsUnprovable(String filename) throws ProblemLoaderException {
        File keyFile = new File(TEST_DIR, filename);
        ProofManagementApi pmapi = KeYApi.loadFromKeyFile(keyFile);
        ProofApi proofApi = pmapi.getLoadedProof();
        Proof proof = proofApi.getProof();
        proofApi.getEnv().getProofControl().startAndWaitForAutoMode(proof);
        // we expect that exactly one branch (the overflow check) is open now:
        Assertions.assertEquals(1, proof.openGoals().size());
    }
}
