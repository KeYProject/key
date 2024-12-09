/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase.po;

import java.io.IOException;
import java.util.Map;
import javax.xml.parsers.ParserConfigurationException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

import org.key_project.util.java.StringUtil;

import org.junit.jupiter.api.Test;
import org.xml.sax.SAXException;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests for {@link ProgramMethodPO}.
 *
 * @author Martin Hentschel
 */
public class TestProgramMethodPO extends AbstractSymbolicExecutionTestCase {
    /**
     * Tests {@code complicatedMethod} without precondition.
     */
    @Test
    public void testComplicatedInnerMethod() throws Exception {
        doTest("/set/fullqualifiedTypeNamesTest/test/my/packageName/TheClass.java",
            "my.packageName.TheClass.TheInnerClass", "complicatedInnerMethod",
            "/set/fullqualifiedTypeNamesTest/oracle/TheInnerClass_complicatedInnerMethod.xml", null,
            "{result_complicatedInnerMethod=self.complicatedInnerMethod(z,a,b,x,o,ac)@my.packageName.TheClass.TheInnerClass; }");
    }

    /**
     * Tests {@code complicatedMethod} with precondition.
     */
    @Test
    public void testComplicatedMethod_Precondition() throws Exception {
        doTest("/set/fullqualifiedTypeNamesTest/test/my/packageName/TheClass.java",
            "my.packageName.TheClass", "complicatedMethod",
            "/set/fullqualifiedTypeNamesTest/oracle/TheClass_complicatedMethod.xml",
            "a == 2 && b && x != null && \"Hello\" == x",
            "{result_complicatedMethod=self.complicatedMethod(i,a,b,x,o,ac,acArray)@my.packageName.TheClass; }");
    }

    /**
     * Tests {@code complicatedMethod} without precondition.
     */
    @Test
    public void testComplicatedMethod() throws IOException, ProofInputException,
            ParserConfigurationException, SAXException, ProblemLoaderException {
        doTest("/set/fullqualifiedTypeNamesTest/test/my/packageName/TheClass.java",
            "my.packageName.TheClass", "complicatedMethod",
            "/set/fullqualifiedTypeNamesTest/oracle/TheClass_complicatedMethod.xml", null,
            "{result_complicatedMethod=self.complicatedMethod(i,a,b,x,o,ac,acArray)@my.packageName.TheClass; }");
    }

    /**
     * Tests {@code returnMethod} with precondition.
     */
    @Test
    public void testReturnMethod_Precondition() throws IOException, ProofInputException,
            ParserConfigurationException, SAXException, ProblemLoaderException {
        doTest("/set/methodPOTest/test/MethodPOTest.java", "MethodPOTest", "returnMethod",
            "/set/methodPOTest/oracle/MethodPOTest_returnMethod_ParamNotNull.xml", "param != null",
            "{result_returnMethod=MethodPOTest.returnMethod(param)@MethodPOTest; }");
    }

    /**
     * Tests {@code returnMethod} without precondition.
     */
    @Test
    public void testReturnMethod() throws IOException, ProofInputException,
            ParserConfigurationException, SAXException, ProblemLoaderException {
        doTest("/set/methodPOTest/test/MethodPOTest.java", "MethodPOTest", "returnMethod",
            "/set/methodPOTest/oracle/MethodPOTest_returnMethod.xml", null,
            "{result_returnMethod=MethodPOTest.returnMethod(param)@MethodPOTest; }");
    }

    /**
     * Tests {@code voidMethod} with precondition.
     */
    @Test
    public void testVoidMethod_Precondition() throws Exception {
        doTest("/set/methodPOTest/test/MethodPOTest.java", "MethodPOTest", "voidMethod",
            "/set/methodPOTest/oracle/MethodPOTest_voidMethod_ParamNotNull.xml", "param != null",
            "{MethodPOTest.voidMethod(param)@MethodPOTest; }");
    }

    /**
     * Tests {@code voidMethod} without precondition.
     */
    @Test
    public void testVoidMethod() throws Exception {
        doTest("/set/methodPOTest/test/MethodPOTest.java", "MethodPOTest", "voidMethod",
            "/set/methodPOTest/oracle/MethodPOTest_voidMethod.xml", null,
            "{MethodPOTest.voidMethod(param)@MethodPOTest; }");
    }

    /**
     * Executes the test steps of all contained test methods.
     */
    protected void doTest(String javaPathInkeyRepDirectory, String containerTypeName,
            String methodFullName, String oraclePathInBaseDirFile, String precondition,
            String expectedTryContent) throws ProofInputException, IOException,
            ParserConfigurationException, SAXException, ProblemLoaderException {
        Map<String, String> originalTacletOptions = null;
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
        boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
        try {
            // Make sure that the correct taclet options are defined.
            originalTacletOptions = setDefaultTacletOptions(testCaseDirectory,
                javaPathInkeyRepDirectory, containerTypeName, methodFullName);
            setOneStepSimplificationEnabled(null, true);
            // Create proof environment for symbolic execution
            env = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory,
                containerTypeName, methodFullName, precondition, false, false, false, false, false,
                false, false, false, false, true);
            // Extract and test try content
            String tryContent = getTryContent(env.getProof());
            assertTrue(StringUtil.equalIgnoreWhiteSpace(expectedTryContent, tryContent),
                "Expected \"" + expectedTryContent + "\" but is \"" + tryContent + "\".");
            // Resume
            resume(env.getUi(), env.getBuilder(), oraclePathInBaseDirFile, testCaseDirectory);
            // Test save and reload of the proof
            assertSaveAndReload(testCaseDirectory, javaPathInkeyRepDirectory,
                oraclePathInBaseDirFile, env);
        } finally {
            // Restore original options
            setOneStepSimplificationEnabled(null, originalOneStepSimplification);
            restoreTacletOptions(originalTacletOptions);
            if (env != null) {
                env.dispose();
            }
        }
    }
}
