/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase.po;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodSubsetPO;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

import org.key_project.util.java.StringUtil;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests for {@link ProgramMethodSubsetPO}.
 *
 * @author Martin Hentschel
 */
public class TestProgramMethodSubsetPO extends AbstractSymbolicExecutionTestCase {
    /**
     * Tests {@code x-=42;return x;} of {@code doSomething} with precondition.
     */
    @Test
    public void testDoSomethingElseBranch() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest",
            "doSomething",
            "/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_elsebranch.xml", null,
            Position.newOneBased(24, 27), Position.newOneBased(25, 33),
            "{method-frame(result->result_doSomething, source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self) { x-=42;return x; } }");
    }

    /**
     * Tests {@code x=x*-1; x+=2;} of {@code doSomething} with precondition.
     */
    @Test
    public void testDoSomethingIfBranch() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest",
            "doSomething", "/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_ifbranch.xml",
            null, Position.newOneBased(20, 27), Position.newOneBased(21, 31),
            "{method-frame(source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self) { x=x*-1; x+=2; } }");
    }

    /**
     * Tests
     * {@code {method-frame(source=doSomething(int, String, boolean)@MethodPartPOTest,this=self) {if (asdf<0)
     * { x=x*-1; x+=2; }else { x-=42;return x; } } }} of {@code doSomething} with precondition.
     */
    @Test
    public void testDoSomethingIf() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest",
            "doSomething", "/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_if.xml", null,
            Position.newOneBased(19, 17), Position.newOneBased(26, 17),
            "{method-frame(source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self) {if (asdf<0) { x=x*-1; x+=2; }else  { x-=42;return x; } } }");
    }

    /**
     * Tests
     * {@code {method-frame(source=doSomething(int, String, boolean)@MethodPartPOTest,this=self) {int x = 0;if (asdf<0)
     * { x=x*-1; x+=2; }else { x-=42;return x; } x=1*asdf; } }} of {@code doSomething} with
     * precondition.
     */
    @Test
    public void testDoSomethingIfWithSurroundingStatements() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest",
            "doSomething",
            "/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_if_surroundingStatements.xml",
            null, Position.newOneBased(17, 63), Position.newOneBased(27, 29),
            "{method-frame(source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self) {int x = 0;if (asdf<0) { x=x*-1; x+=2; }else  { x-=42;return x; } x=1*asdf; } }");
    }

    /**
     * Tests
     * {@code x=1*asdf;int y = 2+CONSTANT+field;int doubleValue = doubleValue(x);int z = x+y+doubleValue; return z;}
     * of {@code doSomething} with precondition.
     */
    @Test
    public void testDoSomethingWithReturn_Precondition() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest",
            "doSomething",
            "/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_withReturn_precondition.xml",
            "x == 1 && asdf == 2 && this.field == 3", Position.newOneBased(27, 19),
            Position.newOneBased(31, 25),
            "{method-frame(result->result_doSomething, source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self) { x=1*asdf;int y = 2+MethodPartPOTest.CONSTANT+this.field;int doubleValue = doubleValue(x);int z = x+y+doubleValue;return z; } }");
    }

    /**
     * Tests
     * {@code x=1*asdf;int y = 2+CONSTANT+field;int doubleValue = doubleValue(x);int z = x+y+doubleValue; return z;}
     * of {@code doSomething} without precondition.
     */
    @Test
    public void testDoSomethingWithReturn() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest",
            "doSomething",
            "/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_withReturn.xml", null,
            Position.newOneBased(27, 19), Position.newOneBased(31, 25),
            "{method-frame(result->result_doSomething, source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self) { x=1*asdf;int y = 2+MethodPartPOTest.CONSTANT+this.field;int doubleValue = doubleValue(x);int z = x+y+doubleValue;return z; } }");
    }

    /**
     * Tests
     * {@code x=1*asdf;int y = 2+CONSTANT+field;int doubleValue = doubleValue(x);int z = x+y+doubleValue;}
     * of {@code doSomething} with precondition.
     */
    @Test
    public void testDoSomethingNoReturn_Precondition() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest",
            "doSomething",
            "/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_noReturn_precondition.xml",
            "x == 1 && asdf == 2 && this.field == 3", Position.newOneBased(27, 19),
            Position.newOneBased(30, 44),
            "{method-frame(source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self) { x=1*asdf;int y = 2+MethodPartPOTest.CONSTANT+this.field;int doubleValue = doubleValue(x);int z = x+y+doubleValue; } }");
    }

    /**
     * Tests
     * {@code x=1*asdf;int y = 2+CONSTANT+field;int doubleValue = doubleValue(x);int z = x+y+doubleValue;}
     * of {@code doSomething} without precondition.
     */
    @Test
    public void testDoSomethingNoReturn() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest",
            "doSomething", "/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_noReturn.xml",
            null, Position.newOneBased(27, 19), Position.newOneBased(30, 44),
            "{method-frame(source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self) { x=1*asdf;int y = 2+MethodPartPOTest.CONSTANT+this.field;int doubleValue = doubleValue(x);int z = x+y+doubleValue; } }");
    }

    /**
     * Tests {@code int b = 3*y;return ;} of {@code voidMethod} with precondition.
     */
    @Test
    public void testVoidMethodWithReturn_Precondition() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest", "voidMethod",
            "/set/methodPartPOTest/oracle/MethodPartPOTest_voidMethod_withReturn_precondition.xml",
            "y == -2", Position.newOneBased(11, 22), Position.newOneBased(13, 31),
            "{method-frame(source=voidMethod(boolean, int)@MethodPartPOTest,this=self) {int b = 3*y;return ; } }");
    }

    /**
     * Tests {@code int b = 3*y;return ;} of {@code voidMethod} without precondition.
     */
    @Test
    public void testVoidMethodWithReturn() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest", "voidMethod",
            "/set/methodPartPOTest/oracle/MethodPartPOTest_voidMethod_withReturn.xml", null,
            Position.newOneBased(11, 22), Position.newOneBased(13, 31),
            "{method-frame(source=voidMethod(boolean, int)@MethodPartPOTest,this=self) {int b = 3*y;return ; } }");
    }

    /**
     * Tests {@code int a = 2 * y;} of {@code voidMethod} with precondition.
     */
    @Test
    public void testVoidMethodNoReturn_Precondition() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest", "voidMethod",
            "/set/methodPartPOTest/oracle/MethodPartPOTest_voidMethod_noReturn_precondition.xml",
            "y == 2", Position.newOneBased(8, 24), Position.newOneBased(9, 38),
            "{method-frame(source=voidMethod(boolean, int)@MethodPartPOTest,this=self) {int a = 2*y; } }");
    }

    /**
     * Tests {@code int a = 2 * y;} of {@code voidMethod} without precondition.
     */
    @Test
    public void testVoidMethodNoReturn() throws Exception {
        doTest("/set/methodPartPOTest/test/MethodPartPOTest.java", "MethodPartPOTest", "voidMethod",
            "/set/methodPartPOTest/oracle/MethodPartPOTest_voidMethod_noReturn.xml", null,
            Position.newOneBased(8, 24), Position.newOneBased(9, 38),
            "{method-frame(source=voidMethod(boolean, int)@MethodPartPOTest,this=self) {int a = 2*y; } }");
    }

    /**
     * Executes the test steps of all contained test methods.
     */
    protected void doTest(String javaPathInkeyRepDirectory, String containerTypeName,
            String methodFullName, String oraclePathInBaseDirFile, String precondition,
            Position startPosition, Position endPosition, String expectedTryContent)
            throws Exception {
        // Create proof environment for symbolic execution
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env =
            createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory,
                containerTypeName, methodFullName, precondition, startPosition, endPosition, false,
                false, false, false, false, false, false, false, false, true);
        try {
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
            env.dispose();
        }
    }
}
