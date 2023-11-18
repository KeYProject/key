/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.io.File;
import java.util.stream.Stream;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

public class ContractLoadingTests {
    public static final File EXAMPLES_DIR = new File("../key.ui/examples/");

    static Stream<Arguments> files() {
        return Stream.of(
            new File(EXAMPLES_DIR, "heap/vstte10_01_SumAndMax/src/SumAndMax.java"),
            new File(HelperClassForTests.TESTCASE_DIRECTORY, "issues/1658/Test.java"),
            new File(HelperClassForTests.TESTCASE_DIRECTORY, "specMath/java/Test.java"),
            new File(HelperClassForTests.TESTCASE_DIRECTORY, "specMath/bigint/Test.java"))
                .map(Arguments::of);
    }

    @ParameterizedTest
    @MethodSource("files")
    void issues1717() throws ProblemLoaderException, ProofInputException {
        File javaFile =
            new File(HelperClassForTests.TESTCASE_DIRECTORY, "issues/1717/UnderscoreZero.java");
        Assumptions.assumeTrue(javaFile.exists());

        KeYEnvironment<?> env = KeYEnvironment.load(javaFile);
        Assertions.assertFalse(env.getAvailableContracts().isEmpty());
        var proof =
            env.createProof(env.getAvailableContracts().get(0).createProofObl(env.getInitConfig()));
        Assertions.assertNotNull(proof);
    }

    @Test
    public void nonEmptyContract(File javaFile) throws ProblemLoaderException {
        KeYEnvironment<?> env = KeYEnvironment.load(javaFile);
        Assertions.assertFalse(env.getAvailableContracts().isEmpty());
    }
}
