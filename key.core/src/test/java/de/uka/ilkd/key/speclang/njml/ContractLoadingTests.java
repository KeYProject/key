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
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
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
     * The fixtures rely on class-level {@code spec_java_math}/{@code spec_bigint_math} JML
     * pragmas (JMLtk parses them as JML modifiers, KeY maps them to {@code ModifierKind}
     * {@code JML_SPEC_*}, and {@code JMLInfoExtractor} turns them into the spec math mode),
     * on model methods with inline {@code spec_*_math} modifiers, and on method-level JML
     * modifier pragmas. The math mode drives overload resolution of
     * {@code Test.accept(1 + 2)} between {@code accept(int)} and {@code accept(\bigint)}.
     */
    @Test
    public void specMathJavaMathTest() throws ProblemLoaderException {
        final Path javaFile =
            HelperClassForTests.TESTCASE_DIRECTORY.resolve("specMath/java/Test.java");
        Assumptions.assumeTrue(Files.exists(javaFile));
        KeYEnvironment<?> file = KeYEnvironment.load(javaFile);
        Assertions.assertFalse(file.getProofContracts().isEmpty());
    }

    @Test
    public void specMathBigintMathTest() throws ProblemLoaderException {
        final Path javaFile =
            HelperClassForTests.TESTCASE_DIRECTORY.resolve("specMath/bigint/Test.java");
        Assumptions.assumeTrue(Files.exists(javaFile));
        KeYEnvironment<?> file = KeYEnvironment.load(javaFile);
        Assertions.assertFalse(file.getProofContracts().isEmpty());
    }

    /**
     * A named spec case in the JMLtk-native form {@code [behavior] <name>:} must carry its name
     * through to the operation contract: JmlToTextual maps {@code JmlContract.name} to the
     * TextualJMLSpecCase name, and JMLSpecFactory.generateName uses it as the contract's base
     * name instead of the generated default.
     */
    @Test
    public void nameClauseCarriesContractName() throws ProblemLoaderException {
        final Path javaFile =
            HelperClassForTests.TESTCASE_DIRECTORY.resolve("speclang/njml/NameClause.java");
        Assumptions.assumeTrue(Files.exists(javaFile));
        KeYEnvironment<?> file = KeYEnvironment.load(javaFile);
        Assertions.assertTrue(file.getProofContracts().stream()
                .filter(FunctionalOperationContract.class::isInstance)
                .map(FunctionalOperationContract.class::cast)
                .anyMatch(c -> "CaseA".equals(c.getBaseName())),
            "expected a functional operation contract with base name 'CaseA', got: "
                + file.getProofContracts());
    }
}
