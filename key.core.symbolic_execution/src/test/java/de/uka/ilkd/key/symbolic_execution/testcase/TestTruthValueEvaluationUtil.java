/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase;

import java.util.*;
import java.util.Map.Entry;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.BranchResult;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.MultiEvaluationResult;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.TruthValue;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.TruthValueTracingResult;
import de.uka.ilkd.key.symbolic_execution.model.*;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

import org.junit.jupiter.api.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Tests for {@link TruthValueTracingUtil}.
 *
 * @author Martin Hentschel
 */
@TestMethodOrder(MethodOrderer.MethodName.class)
public class TestTruthValueEvaluationUtil extends AbstractSymbolicExecutionTestCase {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(TestTruthValueEvaluationUtil.class);

    /**
     * Tests example: /set/truthValueWeakeningTest
     */
    @Test
    public void testJoinTestAfterBranchConditionWithWeakeningGoal() throws Exception {
        // Create expected results
        ExpectedBranchResult seGoal = new ExpectedBranchResult();
        ExpectedBranchResult weakeningGoal =
            new ExpectedBranchResult(new ExpectedTruthValueResult("13.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("12.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("17.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.FALSE));
        ExpectedTruthValueEvaluationResult seResult =
            new ExpectedTruthValueEvaluationResult(seGoal);
        ExpectedTruthValueEvaluationResult weakeningResult =
            new ExpectedTruthValueEvaluationResult(weakeningGoal);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueWeakeningTest/test/JoinTestAfterBranchConditionWithWeakeningGoal.proof",
            "/set/truthValueWeakeningTest/oracle/JoinTestAfterBranchCondition.xml", false, false,
            false, seResult, weakeningResult);
    }

    /**
     * Tests example: /set/truthValueLabelBelowUpdatesDifferentToApplicationTerm
     */
    @Test
    public void testTruthValueLabelBelowUpdatesDifferentToApplicationTerm() throws Exception {
        // Create expected results
        ExpectedBranchResult goal15 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE));
        ExpectedBranchResult goal17 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result =
            new ExpectedTruthValueEvaluationResult(goal15, goal17);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueLabelBelowUpdatesDifferentToApplicationTerm/test/TwoBranch.proof",
            "/set/truthValueLabelBelowUpdatesDifferentToApplicationTerm/oracle/TwoBranch.xml",
            false, false, false, result);
    }

    /**
     * Tests example: /set/truthValueExceptinalAssignableNothingTest
     */
    @Test
    public void testExceptinalAssignableNothingTest_OSS() throws Exception {
        // Create expected results
        ExpectedBranchResult goal374 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE));
        ExpectedBranchResult goal407 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE));
        ExpectedBranchResult goal444 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE));
        ExpectedBranchResult goal475 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE));
        ExpectedBranchResult goal476 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult exceptionResult =
            new ExpectedTruthValueEvaluationResult(goal374, goal407, goal444, goal475, goal476);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueExceptinalAssignableNothingTest/test/ExceptinalAssignableNothingTest_OSS.proof",
            "/set/truthValueExceptinalAssignableNothingTest/oracle/ExceptinalAssignableNothingTest.xml",
            false, false, false, exceptionResult);
    }

    /**
     * Tests example: /set/truthValueExceptinalAssignableNothingTest
     */
    @Test
    public void testExceptinalAssignableNothingTest() throws Exception {
        // Create expected results
        ExpectedBranchResult goal374 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE));
        ExpectedBranchResult goal407 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE));
        ExpectedBranchResult goal444 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE));
        ExpectedBranchResult goal475 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE));
        ExpectedBranchResult goal476 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult exceptionResult =
            new ExpectedTruthValueEvaluationResult(goal374, goal407, goal444, goal475, goal476);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueExceptinalAssignableNothingTest/test/ExceptinalAssignableNothingTest.proof",
            "/set/truthValueExceptinalAssignableNothingTest/oracle/ExceptinalAssignableNothingTest.xml",
            false, false, false, exceptionResult);
    }

    /**
     * Tests example: /set/truthValueBlockContractMagic42
     */
    @Test
    @Disabled
    public void IGNORE_testBlockContractMagic42() throws Exception {
        // Create expected results
        ExpectedBranchResult goal66 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult preconditionResult =
            new ExpectedTruthValueEvaluationResult(goal66);
        ExpectedBranchResult goal62 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("13.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("19.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("20.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("21.0", TruthValue.TRUE));
        ExpectedBranchResult goal64 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("13.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("21.0", TruthValue.FALSE));
        ExpectedTruthValueEvaluationResult validitiyResult =
            new ExpectedTruthValueEvaluationResult(goal62, goal64);
        ExpectedBranchResult goal152 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE));
        ExpectedBranchResult goal154 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("6.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("8.0", TruthValue.FALSE));
        ExpectedTruthValueEvaluationResult usageResult =
            new ExpectedTruthValueEvaluationResult(goal152, goal154);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueBlockContractMagic42/test/BlockContractMagic42.proof",
            "/set/truthValueBlockContractMagic42/oracle/BlockContractMagic42.xml", false, false,
            true, preconditionResult, validitiyResult, usageResult);
    }

    /**
     * Tests example: /set/truthValueRejectedFormula
     */
    @Test
    public void testValueRejectedFormula() throws Exception {
        // Create expected results
        ExpectedBranchResult goal31 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE));
        ExpectedBranchResult goal33 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result =
            new ExpectedTruthValueEvaluationResult(goal31, goal33);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueRejectedFormula/test/LabelLostVerification.proof",
            "/set/truthValueRejectedFormula/oracle/LabelLostVerification.xml", false, false, false,
            result);
    }

    /**
     * Tests example: /set/truthValueAddingOfLabeledSubtree
     */
    @Test
    @Disabled
    public void IGNORE_testAddingOfLabeledSubtree() throws Exception {
        // Create expected results
        ExpectedBranchResult goal53 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("13.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("15.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("16.0", TruthValue.UNKNOWN),
                new ExpectedTruthValueResult("17.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult resultInvInitial =
            new ExpectedTruthValueEvaluationResult(goal53);
        ExpectedBranchResult goal141 = new ExpectedBranchResult();
        ExpectedTruthValueEvaluationResult resultInvTermination =
            new ExpectedTruthValueEvaluationResult(goal141);
        ExpectedBranchResult goal214 = new ExpectedBranchResult();
        ExpectedBranchResult goal229 = new ExpectedBranchResult();
        ExpectedBranchResult goal233 = new ExpectedBranchResult();
        ExpectedBranchResult goal231 = new ExpectedBranchResult();
        ExpectedBranchResult goal216 = new ExpectedBranchResult();
        ExpectedTruthValueEvaluationResult resultNormalTermination =
            new ExpectedTruthValueEvaluationResult(goal214, goal229, goal233, goal231, goal216);
        // Perform test
        doTruthValueEvaluationTest("/set/truthValueAddingOfLabeledSubtree/test/ImmutableList.proof",
            "/set/truthValueAddingOfLabeledSubtree/oracle/ImmutableList.xml", false, false, false,
            resultInvInitial, resultInvTermination, resultNormalTermination);
    }

    /**
     * Tests example: /set/truthValueAssignableAndLoop
     */
    @Test
    @Disabled
    public void IGNORE_testAssignableAndLoop() throws Exception {
        // Create expected results
        ExpectedBranchResult goal430 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("3.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("4.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("6.0", TruthValue.FALSE));
        ExpectedTruthValueEvaluationResult resultExceptionBranch =
            new ExpectedTruthValueEvaluationResult(goal430);
        ExpectedBranchResult goal478 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult resultInvInitial =
            new ExpectedTruthValueEvaluationResult(goal478);
        ExpectedBranchResult goal922 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("19.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("20.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult resultPrecondition =
            new ExpectedTruthValueEvaluationResult(goal922);
        ExpectedBranchResult goal886 = new ExpectedBranchResult();
        ExpectedBranchResult goal869 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("15.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("16.0", TruthValue.TRUE));
        ExpectedBranchResult goal868 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("15.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("16.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult resultLoopEnd =
            new ExpectedTruthValueEvaluationResult(goal868, goal869, goal886);
        ExpectedBranchResult goal1113 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.UNKNOWN),
                new ExpectedTruthValueResult("6.0", TruthValue.UNKNOWN));
        ExpectedBranchResult goal1134 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE));
        ExpectedBranchResult goal1137 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result5 =
            new ExpectedTruthValueEvaluationResult(goal1113, goal1134, goal1137);
        // Perform test
        doTruthValueEvaluationTest("/set/truthValueAssignableAndLoop/test/MagicProofNoOSS.proof",
            "/set/truthValueAssignableAndLoop/oracle/MagicProofNoOSS.xml", true, true, false,
            resultExceptionBranch, resultInvInitial, resultPrecondition, resultLoopEnd, result5);
    }

    /**
     * Tests example: /set/truthValueAnd
     */
    @Test
    public void testAnd3_replaceKnown() throws Exception {
        // Create expected results
        ExpectedBranchResult goal13 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE));
        ExpectedBranchResult goal15 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("2.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result1 =
            new ExpectedTruthValueEvaluationResult(goal13, goal15);
        // Perform test
        doTruthValueEvaluationTest("/set/truthValueAnd/test/And3_replaceKnown.proof",
            "/set/truthValueAnd/oracle/And3_replaceKnown.xml", false, false, false, result1);
    }

    /**
     * Tests example: /set/truthValueUnderstandingProofsMyInteger
     */
    @Test
    public void testUnderstandingProofs_MyInteger() throws Exception {
        // Create expected results
        ExpectedBranchResult goal131 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE));
        ExpectedBranchResult goal133 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("6.0", TruthValue.FALSE));
        ExpectedBranchResult goal150 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result1 =
            new ExpectedTruthValueEvaluationResult(goal131, goal133, goal150);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueUnderstandingProofsMyInteger/test/MyInteger.proof",
            "/set/truthValueUnderstandingProofsMyInteger/oracle/MyInteger.xml", false, false, false,
            result1);
    }

    /**
     * Tests example: /set/truthValueUnderstandingProofsArrayUtil
     */
    @Test
    public void testUnderstandingProofs_ArrayUtil() throws Exception {
        // Create expected results
        ExpectedBranchResult goal87 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("8.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("12.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("13.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("15.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result1 = new ExpectedTruthValueEvaluationResult(goal87);
        ExpectedBranchResult goal175 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("2.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("12.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("14.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result2 =
            new ExpectedTruthValueEvaluationResult(goal175);
        ExpectedBranchResult goal249 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("16.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("17.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("18.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("19.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("24.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("25.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result3 =
            new ExpectedTruthValueEvaluationResult(goal249);
        ExpectedBranchResult goal698 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("26.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("27.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("28.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("29.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("40.0", TruthValue.TRUE));
        ExpectedBranchResult goal747 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("26.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("27.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("28.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("29.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("34.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("40.0", TruthValue.TRUE));
        ExpectedBranchResult goal812 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("26.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("27.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("28.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("29.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("34.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("40.0", TruthValue.TRUE));
        ExpectedBranchResult goal821 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("26.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("27.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("28.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("29.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("38.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("39.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("40.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result4 =
            new ExpectedTruthValueEvaluationResult(goal698, goal747, goal812, goal821);
        ExpectedBranchResult goal1012 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("26.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("27.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("28.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("29.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("34.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("40.0", TruthValue.TRUE));
        ExpectedBranchResult goal1021 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("26.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("27.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("28.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("29.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("38.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("39.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("40.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result5 =
            new ExpectedTruthValueEvaluationResult(goal1012, goal1021);
        ExpectedBranchResult goal1251 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("2.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("12.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("13.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("15.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result6 =
            new ExpectedTruthValueEvaluationResult(goal1251);
        ExpectedBranchResult goal1272 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("8.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("12.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("13.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("15.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result7 =
            new ExpectedTruthValueEvaluationResult(goal1272);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueUnderstandingProofsArrayUtil/test/ArrayUtil.proof",
            "/set/truthValueUnderstandingProofsArrayUtil/oracle/ArrayUtil.xml", false, false, false,
            result1, result2, result3, result4, result5, result6, result7);
    }

    /**
     * Tests example: /set/truthValueUnderstandingProofsAccount
     */
    @Test
    public void testUnderstandingProofs_Account() throws Exception {
        // Create expected results
        ExpectedBranchResult goal246 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("12.0", TruthValue.TRUE));
        ExpectedBranchResult goal248 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("12.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result1 =
            new ExpectedTruthValueEvaluationResult(goal246, goal248);
        ExpectedBranchResult goal195 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("13.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("15.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("16.0", TruthValue.TRUE));
        ExpectedBranchResult goal197 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("13.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("15.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("16.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result2 =
            new ExpectedTruthValueEvaluationResult(goal195, goal197);
        ExpectedBranchResult goal165 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE));
        ExpectedBranchResult goal166 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE));
        ExpectedBranchResult goal168 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result3 =
            new ExpectedTruthValueEvaluationResult(goal165, goal166, goal168);
        ExpectedBranchResult goal224 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("1.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("3.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("4.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("8.0", TruthValue.FALSE));
        ExpectedTruthValueEvaluationResult result4 =
            new ExpectedTruthValueEvaluationResult(goal224);
        // Perform test
        doTruthValueEvaluationTest("/set/truthValueUnderstandingProofsAccount/test/Account.proof",
            "/set/truthValueUnderstandingProofsAccount/oracle/Account.xml", false, false, false,
            result1, result2, result3, result4);
    }

    /**
     * Tests example: /set/truthValueUnderstandingProofsCalendar
     */
    @Test
    public void testUnderstandingProofs_Calendar() throws Exception {
        // Create expected results
        ExpectedBranchResult goal369 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE));
        ExpectedBranchResult goal392 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE));
        ExpectedBranchResult goal423 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("3.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("4.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("8.0", TruthValue.FALSE));
        ExpectedBranchResult goal425 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result1 =
            new ExpectedTruthValueEvaluationResult(goal369, goal392, goal423, goal425);
        ExpectedBranchResult goal611 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("5.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("6.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("8.0", TruthValue.FALSE));
        ExpectedTruthValueEvaluationResult result2 =
            new ExpectedTruthValueEvaluationResult(goal611);
        // Perform test
        doTruthValueEvaluationTest("/set/truthValueUnderstandingProofsCalendar/test/Calendar.proof",
            "/set/truthValueUnderstandingProofsCalendar/oracle/Calendar.xml", false, false, false,
            result1, result2);
    }

    /**
     * Tests example: /set/truthValueMyInteger
     */
    @Test
    public void testMyInteger() throws Exception {
        // Create expected results
        ExpectedBranchResult goal131 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE));
        ExpectedBranchResult goal133 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("6.0", TruthValue.FALSE));
        ExpectedBranchResult goal150 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result =
            new ExpectedTruthValueEvaluationResult(goal131, goal133, goal150);
        // Perform test
        doTruthValueEvaluationTest("/set/truthValueMyInteger/test/MyInteger.proof",
            "/set/truthValueMyInteger/oracle/MyInteger.xml", false, false, false, result);
    }

    /**
     * Tests example: /set/truthValueEquivExample
     */
    @Test
    public void testEquivExample_NoOneStepSimplification() throws Exception {
        // Create expected results
        ExpectedBranchResult goal79 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE));
        ExpectedBranchResult goal91 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.TRUE));
        ExpectedBranchResult goal95 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE));
        ExpectedBranchResult goal97 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("5.0", TruthValue.FALSE)); // SETAccumulate is false
        ExpectedTruthValueEvaluationResult result =
            new ExpectedTruthValueEvaluationResult(goal79, goal91, goal95, goal97);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueEquivExample/test/EquivExampleNoOneStepSimplification.proof",
            "/set/truthValueEquivExample/oracle/EquivExample.xml", false, true, false, result);
    }

    /**
     * Tests example: /set/truthValueIfThenElseIntegerTest
     */
    @Test
    public void testIfThenElseInteger() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult thenResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult elseResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueIfThenElseIntegerTest/test/IfThenElseIntegerTest.java",
            "IfThenElseIntegerTest[IfThenElseIntegerTest::magic(int,int)].JML normal_behavior operation contract.0",
            "/set/truthValueIfThenElseIntegerTest/oracle/IfThenElseIntegerTest.xml", false, false,
            false, thenResult, elseResult);
    }

    /**
     * Tests example: /set/truthValueIfThenElseNotFormulaTest
     */
    @Test
    public void testIfThenElseNotFormula() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult thenResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult elseResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueIfThenElseNotFormulaTest/test/IfThenElseNotFormulaTest.java",
            "IfThenElseNotFormulaTest[IfThenElseNotFormulaTest::magic(int,int)].JML normal_behavior operation contract.0",
            "/set/truthValueIfThenElseNotFormulaTest/oracle/IfThenElseNotFormulaTest.xml", false,
            false, false, thenResult, elseResult);
    }

    /**
     * Tests example: /set/truthValueIfThenElseFormulaTest
     */
    @Test
    public void testIfThenElseFormula() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult thenResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult elseResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueIfThenElseFormulaTest/test/IfThenElseFormulaTest.java",
            "IfThenElseFormulaTest[IfThenElseFormulaTest::magic(int,int)].JML normal_behavior operation contract.0",
            "/set/truthValueIfThenElseFormulaTest/oracle/IfThenElseFormulaTest.xml", false, false,
            false, thenResult, elseResult);
    }

    /**
     * Tests example: /set/truthValueNotLastEvaluationGivesTruthValue
     */
    @Test
    public void testNotLastEvaluationGivesTruthValue() throws Exception {
        // Create expected results
        ExpectedBranchResult goal53 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("4.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.12", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.13", TruthValue.TRUE),
                new ExpectedTruthValueResult("2.0", TruthValue.TRUE));
        ExpectedBranchResult goal41 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("0.0", TruthValue.TRUE));
        ExpectedBranchResult goal39 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("0.0", TruthValue.TRUE));
        ExpectedBranchResult goal55 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.11", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult result =
            new ExpectedTruthValueEvaluationResult(goal53, goal41, goal39, goal55);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueNotLastEvaluationGivesTruthValue/test/NotLastEvaluationGivesTruthValue.proof",
            "/set/truthValueNotLastEvaluationGivesTruthValue/oracle/NotLastEvaluationGivesTruthValue.xml",
            false, true, false, result);
    }

    /**
     * Tests example: /set/truthValueArraySumWhile
     */
    @Test
    public void testArraySumWhile_NoOneStepSimplification() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult initialResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("15.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("16.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("17.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult preservesResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("18.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("19.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("20.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("21.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("22.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("23.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("24.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult terminationResult =
            new ExpectedTruthValueEvaluationResult(
                new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("4.0", TruthValue.FALSE),
                    new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("9.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueArraySumWhile/test/ArraySumWhileNoOneStepSimplification.proof",
            "/set/truthValueArraySumWhile/oracle/ArraySumWhile.xml", false, true, false,
            initialResult, preservesResult, terminationResult);
    }

    /**
     * Tests example: /set/truthValueArraySumWhile
     */
    @Test
    public void testArraySumWhile() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult initialResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("14.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("15.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("16.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("17.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult preservesResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("18.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("19.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("20.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("21.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("22.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("23.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("24.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult terminationResult =
            new ExpectedTruthValueEvaluationResult(
                new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("2.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("3.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("4.0", TruthValue.FALSE),
                    new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("9.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest("/set/truthValueArraySumWhile/test/ArraySumWhile.proof",
            "/set/truthValueArraySumWhile/oracle/ArraySumWhile.xml", false, true, false,
            initialResult, preservesResult, terminationResult);
    }

    /**
     * Tests example: /set/truthValueArrayUtil
     */
    @Test
    @Disabled
    public void IGNORE_testArrayUtil_NoOneStepSimplification() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult goal97 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult goal826 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("17.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("18.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("20.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult goal630 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("13.0", TruthValue.FALSE)));
        ExpectedTruthValueEvaluationResult goal792 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("12.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("13.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult goal1024 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult goal1161 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueArrayUtil/test/ArrayUtilNoOneStepSimplification.proof",
            "/set/truthValueArrayUtil/oracle/ArrayUtil.xml", true, true, false, goal97, goal826,
            goal630, goal792, goal1024, goal1161);
    }

    /**
     * Tests example: /set/truthValueArrayUtil
     */
    @Test
    @Disabled
    public void IGNORE_testArrayUtil() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult goal97 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("6.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult goal826 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("17.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("18.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("20.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult goal630 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("13.0", TruthValue.FALSE)));
        ExpectedTruthValueEvaluationResult goal792 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("8.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("12.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("13.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult goal1024 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult goal1161 = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("3.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest("/set/truthValueArrayUtil/test/ArrayUtil.proof",
            "/set/truthValueArrayUtil/oracle/ArrayUtil.xml", true, true, false, goal97, goal826,
            goal630, goal792, goal1024, goal1161);
    }

    /**
     * Tests example: /set/truthValueSimpleInstanceMethodContractApplication
     */
    @Test
    public void testSimpleInstanceMethodContractApplication_NoOneStepSimplification()
            throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult preResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("12.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult terminationResult =
            new ExpectedTruthValueEvaluationResult(
                new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("5.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueSimpleInstanceMethodContractApplication/test/SimpleInstanceMethodContractApplication_NoOneStepSimplification.proof",
            "/set/truthValueSimpleInstanceMethodContractApplication/oracle/SimpleInstanceMethodContractApplication.xml",
            true, false, false, preResult, terminationResult);
    }

    /**
     * Tests example: /set/truthValueSimpleInstanceMethodContractApplication
     */
    @Test
    public void testSimpleInstanceMethodContractApplication() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult preResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("12.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult terminationResult =
            new ExpectedTruthValueEvaluationResult(
                new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("5.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueSimpleInstanceMethodContractApplication/test/SimpleInstanceMethodContractApplication.proof",
            "/set/truthValueSimpleInstanceMethodContractApplication/oracle/SimpleInstanceMethodContractApplication.xml",
            true, false, false, preResult, terminationResult);
    }

    /**
     * Tests example: /set/truthValueSimpleMethodContractApplication
     */
    @Test
    public void testSimpleMethodContractApplication_NoOneStepSimplification() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult preResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult terminationResult =
            new ExpectedTruthValueEvaluationResult(
                new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("2.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueSimpleMethodContractApplication/test/SimpleMethodContractApplication_NoOneStepSimplification.proof",
            "/set/truthValueSimpleMethodContractApplication/oracle/SimpleMethodContractApplication.xml",
            true, false, false, preResult, terminationResult);
    }

    /**
     * Tests example: /set/truthValueSimpleMethodContractApplication
     */
    @Test
    public void testSimpleMethodContractApplication() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult preResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("10.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("9.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("11.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("7.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult terminationResult =
            new ExpectedTruthValueEvaluationResult(
                new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("1.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("5.0", TruthValue.TRUE),
                    new ExpectedTruthValueResult("2.0", TruthValue.TRUE)));
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueSimpleMethodContractApplication/test/SimpleMethodContractApplication.proof",
            "/set/truthValueSimpleMethodContractApplication/oracle/SimpleMethodContractApplication.xml",
            true, false, false, preResult, terminationResult);
    }

    /**
     * Tests example: /set/truthValueDifferentBranchesTest
     */
    @Test
    public void testDifferentBranchesTest() throws Exception {
        // Create expected results
        ExpectedTruthValueEvaluationResult firstResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult secondResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE)));
        ExpectedTruthValueEvaluationResult thirdResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("1.0", TruthValue.FALSE)));
        ExpectedTruthValueEvaluationResult fourthResult = new ExpectedTruthValueEvaluationResult(
            new ExpectedBranchResult(new ExpectedTruthValueResult("1.0", TruthValue.FALSE)));
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueDifferentBranchesTest/test/DifferentBranchesTest.proof",
            "/set/truthValueDifferentBranchesTest/oracle/DifferentBranchesTest.xml", false, false,
            false, firstResult, secondResult, thirdResult, fourthResult);
    }

    /**
     * Tests example: /set/truthValueMultiplePredicateResults
     */
    @Test
    public void testMultiplePredicateResultsTest() throws Exception {
        // Create expected results
        ExpectedBranchResult goal102 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.FALSE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE));
        ExpectedBranchResult goal95 =
            new ExpectedBranchResult(new ExpectedTruthValueResult("0.0", TruthValue.TRUE),
                new ExpectedTruthValueResult("1.0", TruthValue.TRUE));
        ExpectedTruthValueEvaluationResult expectedResult =
            new ExpectedTruthValueEvaluationResult(goal102, goal95);
        // Perform test
        doTruthValueEvaluationTest(
            "/set/truthValueMultiplePredicateResults/test/MultiplePredicateResultsTest.java",
            "MultiplePredicateResultsTest[MultiplePredicateResultsTest::main(MultiplePredicateResultsTest,MultiplePredicateResultsTest)].JML normal_behavior operation contract.0",
            "/set/truthValueMultiplePredicateResults/oracle/MultiplePredicateResultsTest.xml",
            false, false, false, expectedResult);
    }

    /**
     * Performs an {@link TruthValueTracingUtil} test.
     *
     * @param proofFilePathInBaseDir The path to the java file inside the base directory.
     * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
     * @param useOperationContracts Use operation contracts?
     * @param useLoopInvariants Use loop invariants?
     * @param blockTreatmentContract Block contracts or expand otherwise?
     * @param expectedResults The expected results.
     * @throws Exception Occurred Exception.
     */
    protected void doTruthValueEvaluationTest(String proofFilePathInBaseDir,
            String oraclePathInBaseDirFile, boolean useOperationContracts,
            boolean useLoopInvariants, boolean blockTreatmentContract,
            ExpectedTruthValueEvaluationResult... expectedResults) throws Exception {
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
        try {
            // Perform symbolic execution
            env = doSETTest(testCaseDirectory, proofFilePathInBaseDir, oraclePathInBaseDirFile,
                false, false, false, false, false, useOperationContracts, useLoopInvariants,
                blockTreatmentContract, false, false, false, false, false, true, true);
            assertNotNull(env);
            // Evaluate truth values
            doTruthValueEvaluationTest(env, expectedResults);
        } finally {
            if (env != null) {
                env.dispose();
            }
        }
    }

    /**
     * Performs an {@link TruthValueTracingUtil} test.
     *
     * @param javaPathInBaseDir The path to the java file inside the base directory.
     * @param baseContractName The name of the contract.
     * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
     * @param useOperationContracts Use operation contracts?
     * @param useLoopInvariants Use loop invariants?
     * @param blockTreatmentContract Block contracts or expand otherwise?
     * @param expectedResults The expected results.
     * @throws Exception Occurred Exception.
     */
    protected void doTruthValueEvaluationTest(String javaPathInBaseDir, String baseContractName,
            String oraclePathInBaseDirFile, boolean useOperationContracts,
            boolean useLoopInvariants, boolean blockTreatmentContract,
            ExpectedTruthValueEvaluationResult... expectedResults) throws Exception {
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
        try {
            // Perform symbolic execution
            env = doSETTest(testCaseDirectory, javaPathInBaseDir, baseContractName,
                oraclePathInBaseDirFile, false, false, false, false, ALL_IN_ONE_RUN, false,
                useOperationContracts, useLoopInvariants, blockTreatmentContract, false, false,
                false, false, false, true, true);
            // Evaluate truth values
            doTruthValueEvaluationTest(env, expectedResults);
        } finally {
            if (env != null) {
                env.dispose();
            }
        }
    }

    /**
     * Performs an {@link TruthValueTracingUtil} test.
     *
     * @param env The {@link SymbolicExecutionEnvironment} to use.
     * @param expectedResults The expected results.
     * @throws Exception Occurred Exception.
     */
    protected void doTruthValueEvaluationTest(
            SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env,
            ExpectedTruthValueEvaluationResult... expectedResults) throws Exception {
        // Compute current results
        List<TruthValueTracingResult> currentResults = new LinkedList<>();
        ExecutionNodePreorderIterator iter =
            new ExecutionNodePreorderIterator(env.getBuilder().getStartNode());
        while (iter.hasNext()) {
            IExecutionNode<?> next = iter.next();
            Node nodeToEvaluate;
            if (next instanceof IExecutionTermination) {
                nodeToEvaluate = next.getProofNode();
            } else if (next instanceof IExecutionOperationContract) {
                nodeToEvaluate = next.getProofNode().child(2); // Precondition branch
            } else if (next instanceof IExecutionLoopInvariant) {
                nodeToEvaluate = next.getProofNode().child(0); // Initial
            } else if (next instanceof IExecutionAuxiliaryContract) {
                nodeToEvaluate = next.getProofNode().child(1); // Precondition branch
            } else if (next instanceof IExecutionJoin) {
                nodeToEvaluate = next.getProofNode().child(0); // Weakening branch
            } else {
                nodeToEvaluate = null;
            }
            if (nodeToEvaluate != null) {
                TruthValueTracingResult result = TruthValueTracingUtil.evaluate(nodeToEvaluate,
                    FormulaTermLabel.NAME, false, false);
                currentResults.add(result);
                if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
                    LOGGER.info("Found Result: {}", result);
                }
            }
        }
        // Compare results
        assertResults(expectedResults, currentResults);
    }

    /**
     * Asserts the results.
     *
     * @param expected The expected results.
     * @param current The current results.
     */
    protected void assertResults(ExpectedTruthValueEvaluationResult[] expected,
            List<TruthValueTracingResult> current) {
        Assertions.assertEquals(expected.length, current.size());
        int i = 0;
        Iterator<TruthValueTracingResult> currentIter = current.iterator();
        while (i < expected.length && currentIter.hasNext()) {
            assertTruthValueResults(expected[i], currentIter.next());
            i++;
        }
        Assertions.assertEquals(expected.length, i);
        Assertions.assertFalse(currentIter.hasNext());
    }

    /**
     * Asserts the truth value results.
     *
     * @param expected The expected results.
     * @param current The current results.
     */
    protected void assertTruthValueResults(ExpectedTruthValueEvaluationResult expected,
            TruthValueTracingResult current) {
        BranchResult[] currentResults = current.getBranchResults();
        Assertions.assertEquals(expected.branchResults.length, currentResults.length);
        for (int i = 0; i < currentResults.length; i++) {
            assertBranchResult(expected.branchResults[i], currentResults[i]);
        }
    }

    /**
     * Asserts the branch results.
     *
     * @param expected The expected results.
     * @param current The current results.
     */
    protected void assertBranchResult(ExpectedBranchResult expected, BranchResult current) {
        Map<String, MultiEvaluationResult> currentResults = current.getResults();
        Assertions.assertTrue(expected.labelResults.size() <= currentResults.size(),
            "To many expected results at goal " + current.getLeafNode().serialNr());
        for (Entry<String, TruthValue> expectedEntry : expected.labelResults.entrySet()) {
            MultiEvaluationResult currentInstruction = currentResults.get(expectedEntry.getKey());
            assertNotNull(currentInstruction, "Current result of " + expectedEntry.getKey()
                + " is missing at goal " + current.getLeafNode().serialNr() + ".");
            TruthValue currentResult =
                currentInstruction.evaluate(current.getTermLabelName(), currentResults);
            TruthValue expectedValue = expectedEntry.getValue();
            if (expectedValue == null) {
                Assertions.assertNull(currentResult);
            } else {
                assertNotNull(currentResult, "Current result of " + expectedEntry.getKey()
                    + " at goal " + current.getLeafNode().serialNr() + " is not available.");
                Assertions.assertEquals(expectedValue, currentResult,
                    "Wrong truth value of " + expectedEntry.getKey() + " at goal "
                        + current.getLeafNode().serialNr() + ".");
            }
        }
    }

    /**
     * Represents an expected evaluation result.
     *
     * @author Martin Hentschel
     */
    protected static class ExpectedTruthValueEvaluationResult {
        /**
         * The expected branches.
         */
        private final ExpectedBranchResult[] branchResults;

        /**
         * Constructor.
         *
         * @param branchResults The expected branches.
         */
        public ExpectedTruthValueEvaluationResult(ExpectedBranchResult... branchResults) {
            this.branchResults = branchResults;
        }
    }

    /**
     * Represents an expected branch result.
     *
     * @author Martin Hentschel
     */
    protected static class ExpectedBranchResult {
        /**
         * The truth values of all labels.
         */
        private final Map<String, TruthValue> labelResults = new HashMap<>();

        /**
         * Constructor.
         *
         * @param labelResults The truth values of all labels.
         */
        public ExpectedBranchResult(ExpectedTruthValueResult... labelResults) {
            for (ExpectedTruthValueResult result : labelResults) {
                this.labelResults.put(result.labelId, result.value);
            }
        }
    }

    /**
     * Represents an expected truth value result of a particular label ID.
     *
     * @author Martin Hentschel
     */
    protected static class ExpectedTruthValueResult {
        /**
         * The label ID.
         */
        private final String labelId;

        /**
         * The truth value.
         */
        private final TruthValue value;

        /**
         * Constructor.
         *
         * @param labelId The label ID.
         * @param value The truth value.
         */
        public ExpectedTruthValueResult(String labelId, TruthValue value) {
            this.labelId = labelId;
            this.value = value;
        }
    }
}
