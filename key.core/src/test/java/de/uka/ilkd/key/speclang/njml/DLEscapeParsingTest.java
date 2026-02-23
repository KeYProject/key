/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

public class DLEscapeParsingTest {
    @Test
    public void dlEscapeParsingTest() throws ProblemLoaderException, ProofInputException {
        final Path keyFile = HelperClassForTests.TESTCASE_DIRECTORY
                .resolve("speclang/dlEscapeParsing/dlEscapeTest.key");
        Assumptions.assumeTrue(Files.exists(keyFile));
        KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        // both contracts are provable automatically within a few steps
        Contract contr = env.getProofContracts().getFirst();
        ContractPO po1 = contr.createProofObl(env.getInitConfig());
        Proof proof1 = env.createProof(po1);
        env.getProofControl().startAndWaitForAutoMode(proof1);
        Assertions.assertTrue(proof1.closed());

        ContractPO po2 = contr.createProofObl(env.getInitConfig());
        Proof proof2 = env.createProof(po2);
        env.getProofControl().startAndWaitForAutoMode(proof2);
        Assertions.assertTrue(proof2.closed());
    }
}
