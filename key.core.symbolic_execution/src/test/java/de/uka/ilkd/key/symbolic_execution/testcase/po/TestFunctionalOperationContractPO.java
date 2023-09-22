/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase.po;

import java.io.IOException;
import java.util.Map;
import javax.xml.parsers.ParserConfigurationException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

import org.key_project.util.java.StringUtil;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.xml.sax.SAXException;

/**
 * Tests the {@link FunctionalOperationContractPO} used for symbolic execution.
 *
 * @author Martin Hentschel
 */
public class TestFunctionalOperationContractPO extends AbstractSymbolicExecutionTestCase {
    /**
     * Tests the contract of method {@code doubleValue}.
     */
    @Test
    public void testDoubleValue() throws Exception {
        doTest("/set/existingContractTest/test/ExistingContractTest.java",
            "ExistingContractTest[ExistingContractTest::doubleValue(int)].JML operation contract.0",
            "/set/existingContractTest/oracle/ExistingContractTest.xml",
            "{result_doubleValue=self.doubleValue(_value)@ExistingContractTest; }");
    }

    /**
     * Executes the test steps of all contained test methods.
     */
    protected void doTest(String javaPathInkeyRepDirectory, String baseContractName,
            String oraclePathInBaseDirFile, String expectedTryContent) throws ProofInputException,
            IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
        Map<String, String> originalTacletOptions = null;
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
        try {
            // Make sure that the correct taclet options are defined.
            originalTacletOptions = setDefaultTacletOptions(testCaseDirectory,
                javaPathInkeyRepDirectory, baseContractName);
            // Create proof environment for symbolic execution
            env = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory,
                baseContractName, false, false, false, false, false, false, false, false, false,
                false, false);
            // Extract and test try content
            String tryContent = getTryContent(env.getProof());
            if (!StringUtil.equalIgnoreWhiteSpace(expectedTryContent, tryContent)) {
                Assertions.assertEquals(expectedTryContent, tryContent);
            }
            // Resume
            resume(env.getUi(), env.getBuilder(), oraclePathInBaseDirFile, testCaseDirectory);
            // Test save and reload of the proof
            assertSaveAndReload(testCaseDirectory, javaPathInkeyRepDirectory,
                oraclePathInBaseDirFile, env);
        } finally {
            // Restore taclet options
            restoreTacletOptions(originalTacletOptions);
            if (env != null) {
                env.dispose();
            }
        }
    }
}
