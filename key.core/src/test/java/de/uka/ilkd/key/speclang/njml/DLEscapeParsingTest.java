package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;

public class DLEscapeParsingTest {
    @Test
    public void dlEscapeParsingTest() throws ProblemLoaderException, ProofInputException {
        final Path keyFile = HelperClassForTests.TESTCASE_DIRECTORY
                .resolve("speclang/dlEscapeParsing/dlEscapeTest.key");
        Assumptions.assumeTrue(Files.exists(keyFile));
        KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        Contract contr = env.getProofContracts().getFirst();
        ContractPO po = contr.createProofObl(env.getInitConfig());
        Proof proof = env.createProof(po);
        env.getProofControl().startAndWaitForAutoMode(proof);
        Assertions.assertTrue(proof.closed());
    }
}
