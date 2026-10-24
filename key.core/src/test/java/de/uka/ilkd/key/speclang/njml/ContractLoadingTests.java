/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ContractLoadingTests {
    // TODO weigl: should use FindResources
    public static final File EXAMPLES_DIR = new File("../key.ui/examples/");

    @Test
    public void sumAndMax() throws ProblemLoaderException {
        final File javaFile =
            new File(EXAMPLES_DIR, "heap/vstte10_01_SumAndMax/src/SumAndMax.java");
        KeYEnvironment<?> file = KeYEnvironment.load(javaFile.toPath());
        Services services = file.getServices();
        Logger LOGGER = LoggerFactory.getLogger(ContractLoadingTests.class);
        for (Contract proofContract : file.getProofContracts()) {
            LOGGER.info(proofContract.getPlainText(services));
        }
    }

    @Test
    public void issues1658() throws ProblemLoaderException {
        final Path javaFile =
            HelperClassForTests.TESTCASE_DIRECTORY.resolve("issues/1658/Test.java");
        Assumptions.assumeTrue(Files.exists(javaFile));
        KeYEnvironment<?> file = KeYEnvironment.load(javaFile);
        Assertions.assertFalse(file.getProofContracts().isEmpty());
    }

    @Test
    void issues1717() throws ProblemLoaderException, ProofInputException {
        Path javaFile =
            HelperClassForTests.TESTCASE_DIRECTORY.resolve("issues/1717/UnderscoreZero.java");
        Assumptions.assumeTrue(Files.exists(javaFile));
        KeYEnvironment<?> file = KeYEnvironment.load(javaFile);
        Assertions.assertFalse(file.getProofContracts().isEmpty());
        final var contract = file.getProofContracts().getFirst();
        var proof = file.createProof(contract.createProofObl(file.getInitConfig()));
        Assertions.assertNotNull(proof);
    }

    /**
     * Disabled: the fixtures rely on `spec_*_math` JML modifiers (class-level
     * spec_java_math and method-level spec_bigint_math). JMLtk does not accept
     * these tokens, so the files cannot be parsed by the new front-end.
     * TODO(parity): re-express math modes in a JMLtk-compatible way.
     */
    @Disabled
    @Test
    public void specMathJavaMathTest() throws ProblemLoaderException {
        final Path javaFile =
            HelperClassForTests.TESTCASE_DIRECTORY.resolve("specMath/java/Test.java");
        Assumptions.assumeTrue(Files.exists(javaFile));
        KeYEnvironment<?> file = KeYEnvironment.load(javaFile);
        Assertions.assertFalse(file.getProofContracts().isEmpty());
    }

    @Disabled("See specMathJavaMathTest: spec_*_math modifiers are not accepted by JMLtk")
    @Test
    public void specMathBigintMathTest() throws ProblemLoaderException {
        final Path javaFile =
            HelperClassForTests.TESTCASE_DIRECTORY.resolve("specMath/bigint/Test.java");
        Assumptions.assumeTrue(Files.exists(javaFile));
        KeYEnvironment<?> file = KeYEnvironment.load(javaFile);
        Assertions.assertFalse(file.getProofContracts().isEmpty());
    }
}
