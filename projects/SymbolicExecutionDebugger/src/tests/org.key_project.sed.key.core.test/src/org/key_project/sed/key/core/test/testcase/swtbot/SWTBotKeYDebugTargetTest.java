/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.core.test.testcase.swtbot;

import junit.framework.AssertionFailedError;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IDisconnect;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.test.util.SuspendingStopCondition;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.sed.key.core.test.util.TestSEDKeyCoreUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;

/**
 * Tests for the functionality of a {@link KeYDebugTarget}.
 * @author Martin Hentschel
 */
public class SWTBotKeYDebugTargetTest extends AbstractKeYDebugTargetTestCase {
   /**
    * If the fast mode is enabled the step wise creation of models is disabled.
    */
   private static final boolean FAST_MODE = true;
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testConstraintsOfAppliedMethodContract() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testConstraintsOfAppliedMethodContract",
                     "data/constraintsOfAppliedMethodContract/test",
                     false,
                     createMethodSelector("MethodContract", "magic", "I"),
                     "data/constraintsOfAppliedMethodContract/oracle/MethodContract.xml",
                     true,
                     14,
                     true,
                     true,
                     true,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testNonExecutionBranchHidingSimpleIntQuery_branchHidingSideProofs() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testNonExecutionBranchHidingSimpleIntQuery_branchHidingSideProofs",
                     "data/nonExecutionBranchHidingSimpleIntQuery/test",
                     false,
                     createMethodSelector("SimpleIntQuery", "main", "I"),
                     "data/nonExecutionBranchHidingSimpleIntQuery/oracle/SimpleIntQuery_BranchHidingSideProofs.xml",
                     true,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     true,
                     true, 
                     false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testNonExecutionBranchHidingSimpleIntQuery_branchHidingOff() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testNonExecutionBranchHidingSimpleIntQuery_branchHidingOff",
                     "data/nonExecutionBranchHidingSimpleIntQuery/test",
                     false,
                     createMethodSelector("SimpleIntQuery", "main", "I"),
                     "data/nonExecutionBranchHidingSimpleIntQuery/oracle/SimpleIntQuery_BranchHidingOff.xml",
                     true,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     true,
                     false, 
                     false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testAliasTest_AliasChecksImmediately() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testAliasTest_AliasChecksImmediately",
                     "data/aliasTest/test",
                     false,
                     createMethodSelector("AliasTest", "main", "QIntWrapper;", "QIntWrapper;"),
                     "data/aliasTest/oracle/AliasTest_Immediately.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false, 
                     true);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testAliasTest_AliasChecksNever() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testAliasTest_AliasChecksNever",
                     "data/aliasTest/test",
                     false,
                     createMethodSelector("AliasTest", "main", "QIntWrapper;", "QIntWrapper;"),
                     "data/aliasTest/oracle/AliasTest_Never.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseLoopInvariantArraySumWhile() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useLoopInvariantArraySumWhile",
                     "data/useLoopInvariantArraySumWhile/test",
                     false,
                     createMethodSelector("ArraySumWhile", "sum", "[I"),
                     "data/useLoopInvariantArraySumWhile/oracle/ArraySumWhile.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false, 
                     false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractAllBranchesOpenTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractAllBranchesOpenTest",
                     "data/useOperationContractAllBranchesOpenTest/test",
                     false,
                     createMethodSelector("UseOperationContractAllBranchesOpenTest", "main", "I", "QUseOperationContractAllBranchesOpenTest;"),
                     "data/useOperationContractAllBranchesOpenTest/oracle/UseOperationContractAllBranchesOpenTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractExceptionalNoPreconditionWithNullCheckTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractExceptionalNoPreconditionWithNullCheckTest",
                     "data/useOperationContractExceptionalNoPreconditionWithNullCheckTest/test",
                     false,
                     createMethodSelector("UseOperationContractExceptionalNoPreconditionWithNullCheckTest", "main", "QUseOperationContractExceptionalNoPreconditionWithNullCheckTest;"),
                     "data/useOperationContractExceptionalNoPreconditionWithNullCheckTest/oracle/UseOperationContractExceptionalNoPreconditionWithNullCheckTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractFalsePreconditionTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractFalsePreconditionTest",
                     "data/useOperationContractFalsePreconditionTest/test",
                     false,
                     createMethodSelector("UseOperationContractFalsePreconditionTest", "main"),
                     "data/useOperationContractFalsePreconditionTest/oracle/UseOperationContractExceptionalNoPreconditionWithNullCheckTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractFixedNormalPostTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractFixedNormalPostTest",
                     "data/useOperationContractFixedNormalPostTest/test",
                     false,
                     createMethodSelector("UseOperationContractFixedNormalPostTest", "main"),
                     "data/useOperationContractFixedNormalPostTest/oracle/UseOperationContractFixedNormalPostTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractInvalidPreconditionOnObjectTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractInvalidPreconditionOnObjectTest",
                     "data/useOperationContractInvalidPreconditionOnObjectTest/test",
                     false,
                     createMethodSelector("UseOperationContractInvalidPreconditionOnObjectTest", "main"),
                     "data/useOperationContractInvalidPreconditionOnObjectTest/oracle/UseOperationContractInvalidPreconditionOnObjectTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractInvalidPreconditionTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractInvalidPreconditionTest",
                     "data/useOperationContractInvalidPreconditionTest/test",
                     false,
                     createMethodSelector("UseOperationContractInvalidPreconditionTest", "main"),
                     "data/useOperationContractInvalidPreconditionTest/oracle/UseOperationContractInvalidPreconditionTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractNoExceptionTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractNoExceptionTest",
                     "data/useOperationContractNoExceptionTest/test",
                     false,
                     createMethodSelector("UseOperationContractNoExceptionTest", "main"),
                     "data/useOperationContractNoExceptionTest/oracle/UseOperationContractNoExceptionTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractNoPreconditionTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractNoPreconditionTest",
                     "data/useOperationContractNoPreconditionTest/test",
                     false,
                     createMethodSelector("UseOperationContractNoPreconditionTest", "main"),
                     "data/useOperationContractNoPreconditionTest/oracle/UseOperationContractNoPreconditionTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractNoPreconditionWithNullCheckTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractNoPreconditionWithNullCheckTest",
                     "data/useOperationContractNoPreconditionWithNullCheckTest/test",
                     false,
                     createMethodSelector("UseOperationContractNoPreconditionWithNullCheckTest", "main", "QUseOperationContractNoPreconditionWithNullCheckTest;"),
                     "data/useOperationContractNoPreconditionWithNullCheckTest/oracle/UseOperationContractNoPreconditionWithNullCheckTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractNormalAndExceptionalBranchTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractNormalAndExceptionalBranchTest",
                     "data/useOperationContractNormalAndExceptionalBranchTest/test",
                     false,
                     createMethodSelector("UseOperationContractNormalAndExceptionalBranchTest", "main", "I"),
                     "data/useOperationContractNormalAndExceptionalBranchTest/oracle/UseOperationContractNormalAndExceptionalBranchTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }

   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testUseOperationContractNormalAndExceptionalTogetherTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_useOperationContractNormalAndExceptionalTogetherTest",
                     "data/useOperationContractNormalAndExceptionalTogetherTest/test",
                     false,
                     createMethodSelector("UseOperationContractNormalAndExceptionalTogetherTest", "main"),
                     "data/useOperationContractNormalAndExceptionalTogetherTest/oracle/UseOperationContractNormalAndExceptionalTogetherTest.xml",
                     false,
                     14,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     true,
                     false,
                     false, 
                     false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testComplexConstructorTest() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testComplexConstructorTest",
                                   "data/complexConstructorTest/test",
                                   false,
                                   createMethodSelector("ComplexConstructorTest", "main"),
                                   "data/complexConstructorTest/oracle/ComplexConstructorTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testSimpleConstructorTest() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testSimpleConstructorTest",
                                   "data/simpleConstructorTest/test",
                                   false,
                                   createMethodSelector("SimpleConstructorTest", "main"),
                                   "data/simpleConstructorTest/oracle/SimpleConstructorTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMagic42() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMagic42",
                     "data/magic42/test",
                     false,
                     createMethodSelector("Magic42", "compute", "I"),
                     "data/magic42/oracle/Magic42.xml",
                     true,
                     14,
                     true,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false, 
                     false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testElseIf_mergeBranchConditions() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testElseIf_mergeBranchConditions",
                                   "data/elseIfTest/test",
                                   false,
                                   createMethodSelector("ElseIfTest", "elseIf", "I"),
                                   "data/elseIfTest/oracleMergeBranchConditions/ElseIfTest.xml",
                                   false,
                                   true);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testSwitchCase_mergeBranchConditions() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testSwitchCase_mergeBranchConditions",
                                   "data/switchCaseTest/test",
                                   false,
                                   createMethodSelector("SwitchCaseTest", "switchCase", "I"),
                                   "data/switchCaseTest/oracleMergeBranchConditions/SwitchCaseTest.xml",
                                   false,
                                   true);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testLoopIteration_LoopWithMethod() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testLoopIteration_LoopWithMethod",
                                   "data/loopIterationTest/test",
                                   false,
                                   createMethodSelector("LoopIterationTest", "loopMultipleTimes"),
                                   "data/loopIterationTest/oracle/LoopIterationTest_loopMultipleTimes.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testLoopIteration_LoopStatementCopied() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testLoopIteration_LoopStatementCopied",
                                   "data/loopIterationTest/test",
                                   false,
                                   createMethodSelector("LoopIterationTest", "mainWorks"),
                                   "data/loopIterationTest/oracle/LoopIterationTest_mainWorks.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testLoopIteration_LoopStatementReused() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testLoopIteration_LoopStatementReused",
                                   "data/loopIterationTest/test",
                                   false,
                                   createMethodSelector("LoopIterationTest", "main"),
                                   "data/loopIterationTest/oracle/LoopIterationTest_main.xml");
   }
   
   /**
    * Tests the handling of variables.
    */
   @Test
   public void testVariablesArrayTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testVariablesArrayTest",
                     "data/variablesArrayTest/test",
                     false,
                     createMethodSelector("VariablesArrayTest", "main"),
                     "data/variablesArrayTest/oracle/VariablesArrayTest.xml",
                     false,
                     8,
                     true,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false, 
                     false);
   }
   
   /**
    * Tests the handling of variables.
    */
   @Test
   public void testVariablesInstanceVariableTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testVariablesInstanceVariableTest",
                     "data/variablesInstanceVariableTest/test",
                     false,
                     createMethodSelector("VariablesInstanceVariableTest", "main", "QIntWrapper;"),
                     "data/variablesInstanceVariableTest/oracle/VariablesInstanceVariableTest.xml",
                     false,
                     8,
                     true,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false, 
                     false);
   }
   
   /**
    * Tests the handling of variables.
    */
   @Test
   public void testVariablesLocalTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testVariablesLocalTest",
                     "data/variablesLocalTest/test",
                     false,
                     createMethodSelector("VariablesLocalTest", "main"),
                     "data/variablesLocalTest/oracle/VariablesLocalTest.xml",
                     false,
                     8,
                     true,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false, 
                     false);
   }
   
   /**
    * Tests the handling of variables.
    */
   @Test
   public void testVariablesStaticTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testVariablesStaticTest",
                     "data/variablesStaticTest/test",
                     false,
                     createMethodSelector("VariablesStaticTest", "main"),
                     "data/variablesStaticTest/oracle/VariablesStaticTest.xml",
                     false,
                     8,
                     true,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false, 
                     false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testSimpleIf_NoMethodReturnValues() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testSimpleIf_NoMethodReturnValues",
                     "data/simpleIf/test",
                     false,
                     createMethodSelector("SimpleIf", "min", "I", "I"),
                     "data/simpleIf/oracle_noMethodReturnValues/SimpleIf.xml",
                     false,
                     false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testThrowVariableTest() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testThrowVariableTest",
                                   "data/throwVariableTest/test",
                                   false,
                                   createMethodSelector("ThrowVariableTest", "main"),
                                   "data/throwVariableTest/oracle/ThrowVariableTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testThrowTest() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testThrowTest",
                                   "data/throwTest/test",
                                   false,
                                   createMethodSelector("ThrowTest", "main"),
                                   "data/throwTest/oracle/ThrowTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testSimpleNullPointerSplitTest() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testSimpleNullPointerSplitTest",
                                   "data/simpleNullPointerSplitTest/test",
                                   false,
                                   createMethodSelector("SimpleNullPointerSplitTest", "main", "QSimpleNullPointerSplitTest;"),
                                   "data/simpleNullPointerSplitTest/oracle/SimpleNullPointerSplitTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testForEach() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testForEach",
                                   "data/forEachTest/test",
                                   false,
                                   createMethodSelector("ForEachTest", "main"),
                                   "data/forEachTest/oracle/ForEachTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testForFalse() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testForFalse",
                                   "data/forFalseTest/test",
                                   false,
                                   createMethodSelector("ForFalseTest", "main"),
                                   "data/forFalseTest/oracle/ForFalseTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFunctionalFor() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testFunctionalFor",
                                   "data/functionalForTest/test",
                                   false,
                                   createMethodSelector("FunctionalForTest", "main"),
                                   "data/functionalForTest/oracle/FunctionalForTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testNestedFor() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testNestedFor",
                                   "data/nestedForTest/test",
                                   false,
                                   createMethodSelector("NestedForTest", "main"),
                                   "data/nestedForTest/oracle/NestedForTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFor() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testFor",
                                   "data/forTest/test",
                                   false,
                                   createMethodSelector("ForTest", "main"),
                                   "data/forTest/oracle/ForTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testDoWhileFalse() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testDoWhileFalse",
                                   "data/doWhileFalseTest/test",
                                   false,
                                   createMethodSelector("DoWhileFalseTest", "main"),
                                   "data/doWhileFalseTest/oracle/DoWhileFalseTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFunctionalDoWhile() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testFunctionalDoWhile",
                                   "data/functionalDoWhileTest/test",
                                   false,
                                   createMethodSelector("FunctionalDoWhileTest", "main"),
                                   "data/functionalDoWhileTest/oracle/FunctionalDoWhileTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testNestedDoWhile() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testNestedDoWhile",
                                   "data/nestedDoWhileTest/test",
                                   false,
                                   createMethodSelector("NestedDoWhileTest", "main"),
                                   "data/nestedDoWhileTest/oracle/NestedDoWhileTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testDoWhile() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testDoWhile",
                                   "data/doWhileTest/test",
                                   false,
                                   createMethodSelector("DoWhileTest", "main"),
                                   "data/doWhileTest/oracle/DoWhileTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testWhileFalse() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testWhileFalse",
                                   "data/whileFalseTest/test",
                                   false,
                                   createMethodSelector("WhileFalseTest", "main"),
                                   "data/whileFalseTest/oracle/WhileFalseTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFunctionalWhile() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testFunctionalWhile",
                                   "data/functionalWhileTest/test",
                                   false,
                                   createMethodSelector("FunctionalWhileTest", "main"),
                                   "data/functionalWhileTest/oracle/FunctionalWhileTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testNestedWhile() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testNestedWhile",
                                   "data/nestedWhileTest/test",
                                   false,
                                   createMethodSelector("NestedWhileTest", "mainNested"),
                                   "data/nestedWhileTest/oracle/NestedWhileTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testWhile() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testWhile",
                                   "data/whileTest/test",
                                   false,
                                   createMethodSelector("WhileTest", "main"),
                                   "data/whileTest/oracle/WhileTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testStatementKinds() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testStatementKinds",
                                   "data/statementKindTest/test",
                                   false,
                                   createMethodSelector("StatementKindTest", "main"),
                                   "data/statementKindTest/oracle/StatementKindTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testSwitchCase() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testSwitchCase",
                                   "data/switchCaseTest/test",
                                   false,
                                   createMethodSelector("SwitchCaseTest", "switchCase", "I"),
                                   "data/switchCaseTest/oracle/SwitchCaseTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testElseIf() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testElseIf",
                                   "data/elseIfTest/test",
                                   false,
                                   createMethodSelector("ElseIfTest", "elseIf", "I"),
                                   "data/elseIfTest/oracle/ElseIfTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallFormatTest() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallFormatTest",
                                   "data/methodFormatTest/test",
                                   false,
                                   createMethodSelector("MethodFormatTest", "main"),
                                   "data/methodFormatTest/oracle/MethodFormatTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFixedRecursiveMethodCall() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testFixedRecursiveMethodCall",
                                   "data/fixedRecursiveMethodCallTest/test",
                                   false,
                                   createMethodSelector("FixedRecursiveMethodCallTest", "decreaseValue"),
                                   "data/fixedRecursiveMethodCallTest/oracle/FixedRecursiveMethodCallTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testElseIfDifferentVariables() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testElseIfDifferentVariables",
                                   "data/elseIfDifferentVariables/test",
                                   false,
                                   createMethodSelector("ElseIfDifferentVariables", "main", "Z", "Z"),
                                   "data/elseIfDifferentVariables/oracle/ElseIfDifferentVariables.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testTryCatchFinally() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testTryCatchFinally",
                                   "data/tryCatchFinally/test",
                                   false,
                                   createMethodSelector("TryCatchFinally", "tryCatchFinally", "I"),
                                   "data/tryCatchFinally/oracle/TryCatchFinally.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testStaticMethodCall() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testStaticMethodCall",
                                   "data/staticMethodCall/test",
                                   false,
                                   createMethodSelector("StaticMethodCall", "main"),
                                   "data/staticMethodCall/oracle/StaticMethodCall.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testComplexIfSteps() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testComplexIfSteps",
                                  "data/complexIf/test",
                                  false,
                                  createMethodSelector("ComplexIf", "min", "I", "I"),
                                  "data/complexIf/oracle/ComplexIf.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testComplexFlatSteps() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testComplexFlatSteps",
                                   "data/complexFlatSteps/test",
                                   false,
                                   createMethodSelector("ComplexFlatSteps", "doSomething"),
                                   "data/complexFlatSteps/oracle/ComplexFlatSteps.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFunctionalIf() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testFunctionalIf",
                                   "data/functionalIf/test",
                                   false,
                                   createMethodSelector("FunctionalIf", "min", "I", "I"),
                                   "data/functionalIf/oracle/FunctionalIf.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testSimpleIf() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testSimpleIf",
                                   "data/simpleIf/test",
                                   false,
                                   createMethodSelector("SimpleIf", "min", "I", "I"),
                                   "data/simpleIf/oracle/SimpleIf.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallOnObjectWithException() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallOnObjectWithException",
                                   "data/methodCallOnObjectWithException/test",
                                   false,
                                   createMethodSelector("MethodCallOnObjectWithException", "main"),
                                   "data/methodCallOnObjectWithException/oracle/MethodCallOnObjectWithException.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallOnObject() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallOnObject",
                                   "data/methodCallOnObject/test",
                                   false,
                                   createMethodSelector("MethodCallOnObject", "main"),
                                   "data/methodCallOnObject/oracle/MethodCallOnObject.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallParallel() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallParallel",
                                   "data/methodCallParallelTest/test",
                                   false,
                                   createMethodSelector("MethodCallParallelTest", "main"),
                                   "data/methodCallParallelTest/oracle/MethodCallParallelTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallHierarchyWithException() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallHierarchyWithException",
                                   "data/methodHierarchyCallWithExceptionTest/test",
                                   false,
                                   createMethodSelector("MethodHierarchyCallWithExceptionTest", "main"),
                                   "data/methodHierarchyCallWithExceptionTest/oracle/MethodHierarchyCallWithExceptionTest.xml",
                                   true,
                                   false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallHierarchy() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallHierarchy",
                                   "data/methodHierarchyCallTest/test",
                                   false,
                                   createMethodSelector("MethodHierarchyCallTest", "main"),
                                   "data/methodHierarchyCallTest/oracle/MethodHierarchyCallTest.xml",
                                   true,
                                   false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFlatStatements() throws Exception {
      assertSEDModelRunAndStepInto("SWTBotKeYDebugTargetSuspendResumeTest_testFlatStatements",
                                   "data/statements/test",
                                   false,
                                   createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"),
                                   "data/statements/oracle/FlatSteps.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget},
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testFlatStatements_ProofIsNoLongerAvailableInKeY() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testFlatStatements_ProofIsNoLongerAvailableInKeY",
                     "data/statements/test",
                     true,
                     createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"),
                     "data/statements/oracle/FlatSteps.xml",
                     false,
                     10, 
                     false, 
                     false, 
                     false,
                     false,
                     true,
                     false,
                     false,
                     false,
                     false, 
                     false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testRecursiveFibonacci10() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testRecursiveFibonacci10",
                     "data/recursiveFibonacci/test",
                     false,
                     createMethodSelector("RecursiveFibonacci", "fibonacci10"),
                     "data/recursiveFibonacci/oracle/RecursiveFibonacci.xml",
                     false,
                     30,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false,
                     false, 
                     false);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget} by
    * resuming the initial state, suspend the progress and finish it
    * with a second resume.
    */
   @Test
   public void testSuspendResumeDebugTarget_Resume_Suspend_Resume() throws Exception {
      IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            // Test launch commands after loading completed
            assertTrue(launch.canTerminate());
            assertFalse(launch.isTerminated());
            assertTrue(target instanceof ISEDDebugTarget);
            assertTrue(target.canDisconnect());
            assertTrue(target.canResume());
            assertFalse(target.canSuspend());
            assertTrue(target.canTerminate());
            assertFalse(target.isDisconnected());
            assertTrue(target.isSuspended());
            assertFalse(target.isTerminated());
            // Make sure that the debug target is in the initial state.
            TestSEDKeyCoreUtil.assertInitialTarget(target, TestSEDKeyCoreUtil.computeTargetName(method));
            // Resume launch
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0); // Select first debug target
            item.contextMenu("Resume").click();
            SuspendingStopCondition sc = new SuspendingStopCondition(true, 1, 1000);
            ((KeYDebugTarget)target).getProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(sc);
            TestSedCoreUtil.waitUntilDebugTargetCanSuspend(bot, target); // Wait until the target is resumed.
            assertTrue(launch.canTerminate());
            assertFalse(launch.isTerminated());
            assertTrue(target.canDisconnect());
            assertFalse(target.canResume());
            assertTrue(target.canSuspend());
            assertTrue(target.canTerminate());
            assertFalse(target.isDisconnected());
            assertFalse(target.isSuspended());
            assertFalse(target.isTerminated());
            // Suspend launch
            TestSedCoreUtil.suspend(bot, target);
            // Make sure that the execution tree is not completed
            AssertionFailedError caughtError = null;
            try {
               TestSEDKeyCoreUtil.assertFlatStepsExample(target);
            }
            catch (AssertionFailedError e) {
               caughtError = e;
            }
            if (caughtError == null) {
               fail("Execution Tree is completed, suspend has not worked.");
            }
            // Resume launch
            item.contextMenu("Resume").click();
            TestSedCoreUtil.waitUntilDebugTargetCanSuspend(bot, target); // Wait until the target is resumed.
            assertTrue(launch.canTerminate());
            assertFalse(launch.isTerminated());
            assertTrue(target.canDisconnect());
            assertFalse(target.canResume());
            assertTrue(target.canSuspend());
            assertTrue(target.canTerminate());
            assertFalse(target.isDisconnected());
            assertFalse(target.isSuspended());
            assertFalse(target.isTerminated());
            TestSedCoreUtil.waitUntilDebugTargetCanResume(bot, target); // wait until the target is suspended.
            assertTrue(launch.canTerminate());
            assertFalse(launch.isTerminated());
            assertTrue(target.canDisconnect());
            assertTrue(target.canResume());
            assertFalse(target.canSuspend());
            assertTrue(target.canTerminate());
            assertFalse(target.isDisconnected());
            assertTrue(target.isSuspended());
            assertFalse(target.isTerminated());
            // Test the execution tree
            TestSEDKeyCoreUtil.assertFlatStepsExample(target);
         }
      };
      doKeYDebugTargetTest("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeDebugTarget_Resume_Suspend_Resume", 
                           "data/statements/test",
                           true,
                           true,
                           createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"),
                           null,
                           null,
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE, 
                           6, executor);
   }
   
   /**
    * Executes {@link #assertSEDModel(String, String, boolean, IMethodSelector, String, boolean)}
    * first with run and second with step into functionality.
    * @param projectName The project name in the workspace.
    * @param pathInBundle The path to the source code in the bundle to extract to the workspace project.
    * @param clearProofListInKeYBeforeResume Clear proof list in KeY before resume?
    * @param selector {@link IMethodSelector} to select an {@link IMethod} to launch.
    * @param expectedModelPathInBundle Path to the oracle file in the bundle which defines the expected {@link ISEDDebugTarget} model.
    * @throws Exception Occurred Exception.
    */
   protected void assertSEDModelRunAndStepInto(String projectName,
                                               String pathInBundle,
                                               boolean clearProofListInKeYBeforeResume,
                                               IMethodSelector selector,
                                               String expectedModelPathInBundle) throws Exception {
      assertSEDModel(projectName, pathInBundle, clearProofListInKeYBeforeResume, selector, expectedModelPathInBundle, false);
      if (!FAST_MODE) {
         assertSEDModel(projectName + "stepInto", pathInBundle, clearProofListInKeYBeforeResume, selector, expectedModelPathInBundle, true);
      }
   }
   
   /**
    * Executes {@link #assertSEDModel(String, String, boolean, IMethodSelector, String, boolean)}
    * first with run and second with step into functionality.
    * @param projectName The project name in the workspace.
    * @param pathInBundle The path to the source code in the bundle to extract to the workspace project.
    * @param clearProofListInKeYBeforeResume Clear proof list in KeY before resume?
    * @param selector {@link IMethodSelector} to select an {@link IMethod} to launch.
    * @param expectedModelPathInBundle Path to the oracle file in the bundle which defines the expected {@link ISEDDebugTarget} model.
    * @param includeCallStack Include call stack?
    * @param mergeBranchConditions Merge branch conditions?
    * @throws Exception Occurred Exception.
    */
   protected void assertSEDModelRunAndStepInto(String projectName,
                                               String pathInBundle,
                                               boolean clearProofListInKeYBeforeResume,
                                               IMethodSelector selector,
                                               String expectedModelPathInBundle,
                                               boolean includeCallStack,
                                               boolean mergeBranchConditions) throws Exception {
      assertSEDModel(projectName, pathInBundle, clearProofListInKeYBeforeResume, selector, expectedModelPathInBundle, false, 8, false, includeCallStack, false, false, false, mergeBranchConditions, false, false, false, false);
      if (!FAST_MODE) {
         assertSEDModel(projectName + "stepInto", pathInBundle, clearProofListInKeYBeforeResume, selector, expectedModelPathInBundle, false, 8, false, includeCallStack, false, true, false, mergeBranchConditions, false, false, false, false);
      }
   }
   
   /**
    * Executes the following test steps:
    * <ol>
    *    <li>Extract code from bundle to a Java project with the defined name in the workspace.</li>
    *    <li>Select an {@link IMethod} to debug with the given {@link IMethodSelector}.</li>
    *    <li>Launch selected {@link IMethod} with the Symbolic Execution Debugger based on KeY.</li>
    *    <li>Make sure that the initial SED model ({@link ISEDDebugTarget}) is opened.</li>
    *    <li>Resume the execution.</li>
    *    <li>Make sure that the final SED model ({@link ISEDDebugTarget}) specified by the oracle file expectedModelPathInBundle is reached.</li>
    * </ol>
    * @param projectName The project name in the workspace.
    * @param pathInBundle The path to the source code in the bundle to extract to the workspace project.
    * @param clearProofListInKeYBeforeResume Clear proof list in KeY before resume?
    * @param selector {@link IMethodSelector} to select an {@link IMethod} to launch.
    * @param expectedModelPathInBundle Path to the oracle file in the bundle which defines the expected {@link ISEDDebugTarget} model.
    * @param stepIntoInsteadOfRun Use step into functionality instead of the run functionality to create the tree?
    * @throws Exception Occurred Exception.
    */
   protected void assertSEDModel(String projectName,
                                 String pathInBundle,
                                 boolean clearProofListInKeYBeforeResume,
                                 IMethodSelector selector,
                                 String expectedModelPathInBundle,
                                 boolean stepIntoInsteadOfRun) throws Exception {
      assertSEDModel(projectName, pathInBundle, clearProofListInKeYBeforeResume, selector, expectedModelPathInBundle, true, stepIntoInsteadOfRun);
   }
   
   /**
    * Executes the following test steps:
    * <ol>
    *    <li>Extract code from bundle to a Java project with the defined name in the workspace.</li>
    *    <li>Select an {@link IMethod} to debug with the given {@link IMethodSelector}.</li>
    *    <li>Launch selected {@link IMethod} with the Symbolic Execution Debugger based on KeY.</li>
    *    <li>Make sure that the initial SED model ({@link ISEDDebugTarget}) is opened.</li>
    *    <li>Resume the execution.</li>
    *    <li>Make sure that the final SED model ({@link ISEDDebugTarget}) specified by the oracle file expectedModelPathInBundle is reached.</li>
    * </ol>
    * @param projectName The project name in the workspace.
    * @param pathInBundle The path to the source code in the bundle to extract to the workspace project.
    * @param clearProofListInKeYBeforeResume Clear proof list in KeY before resume?
    * @param selector {@link IMethodSelector} to select an {@link IMethod} to launch.
    * @param expectedModelPathInBundle Path to the oracle file in the bundle which defines the expected {@link ISEDDebugTarget} model.
    * @param showMethodReturnValues Show method return values?
    * @param stepIntoInsteadOfRun Use step into functionality instead of the run functionality to create the tree?
    * @throws Exception Occurred Exception.
    */
   protected void assertSEDModel(String projectName,
                                 String pathInBundle,
                                 boolean clearProofListInKeYBeforeResume,
                                 IMethodSelector selector,
                                 String expectedModelPathInBundle,
                                 boolean showMethodReturnValues,
                                 boolean stepIntoInsteadOfRun) throws Exception {
      assertSEDModel(projectName, pathInBundle, clearProofListInKeYBeforeResume, selector, expectedModelPathInBundle, showMethodReturnValues, 10, false, false, false, stepIntoInsteadOfRun, false, false, false, false, false, false);
   }
   
   /**
    * Executes the following test steps:
    * <ol>
    *    <li>Extract code from bundle to a Java project with the defined name in the workspace.</li>
    *    <li>Select an {@link IMethod} to debug with the given {@link IMethodSelector}.</li>
    *    <li>Launch selected {@link IMethod} with the Symbolic Execution Debugger based on KeY.</li>
    *    <li>Make sure that the initial SED model ({@link ISEDDebugTarget}) is opened.</li>
    *    <li>Resume the execution.</li>
    *    <li>Make sure that the final SED model ({@link ISEDDebugTarget}) specified by the oracle file expectedModelPathInBundle is reached.</li>
    * </ol>
    * @param projectName The project name in the workspace.
    * @param pathInBundle The path to the source code in the bundle to extract to the workspace project.
    * @param clearProofListInKeYBeforeResume Clear proof list in KeY before resume?
    * @param selector {@link IMethodSelector} to select an {@link IMethod} to launch.
    * @param expectedModelPathInBundle Path to the oracle file in the bundle which defines the expected {@link ISEDDebugTarget} model.
    * @param showMethodReturnValues Show method return values?
    * @param timeoutFactor The timeout factor used to increase {@link SWTBotPreferences#TIMEOUT}.
    * @param includeVariables Include variables?
    * @param includeCallstack Include call stack?
    * @param includeConstraints TODO
    * @param stepIntoInsteadOfRun Use step into functionality instead of the run functionality to create the tree?
    * @param showKeYMainWindow Show KeY's main window?
    * @param mergeBranchConditions Merge branch conditions?
    * @param useMethodContracts Use operation contracts?
    * @param useLoopInvariants Use loop invariants?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @param includeConstraints Include constraints?
    * @throws Exception Occurred Exception.
    */
   protected void assertSEDModel(String projectName,
                                 String pathInBundle,
                                 final boolean clearProofListInKeYBeforeResume,
                                 IMethodSelector selector,
                                 final String expectedModelPathInBundle,
                                 boolean showMethodReturnValues,
                                 int timeoutFactor,
                                 final boolean includeVariables,
                                 final boolean includeCallstack,
                                 final boolean includeConstraints,
                                 final boolean stepIntoInsteadOfRun,
                                 final boolean showKeYMainWindow,
                                 final boolean mergeBranchConditions,
                                 final boolean useMethodContracts,
                                 final boolean useLoopInvariants,
                                 final boolean nonExecutionBranchHidingSideProofs, 
                                 final boolean aliasChecks) throws Exception {
      IKeYDebugTargetTestExecutor executor = createResumeExecutor(clearProofListInKeYBeforeResume, Activator.PLUGIN_ID, expectedModelPathInBundle, includeVariables, includeCallstack, includeConstraints, stepIntoInsteadOfRun, mergeBranchConditions, useMethodContracts, useLoopInvariants, nonExecutionBranchHidingSideProofs, aliasChecks);
      doKeYDebugTargetTest(projectName, 
                           pathInBundle, 
                           true,
                           true,
                           selector, 
                           null,
                           null,
                           Boolean.valueOf(showMethodReturnValues), 
                           Boolean.valueOf(includeVariables),
                           Boolean.valueOf(showKeYMainWindow),
                           Boolean.valueOf(mergeBranchConditions),
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE, 
                           timeoutFactor, executor);
   }

   /**
    * Tests the suspend/resume functionality on the {@link ILaunch}
    * that is disconnected.
    */
   @Test
   public void testSuspendResumeWhileDisconnected_Launch() throws Exception {
      doTestSuspendResumeWhileDisconnected("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeWhileDisconnected_Launch",
                                           false,
                                           0);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}
    * that is disconnected.
    */
   @Test
   public void testSuspendResumeWhileDisconnected_DebugTarget() throws Exception {
      doTestSuspendResumeWhileDisconnected("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeWhileDisconnected_DebugTarget",
                                           false,
                                           0, 0);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link ILaunch}
    * that is disconnected,
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testSuspendResumeWhileDisconnected_Launch_ProofIsNoLongerAvailableInKeY() throws Exception {
      doTestSuspendResumeWhileDisconnected("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeWhileDisconnected_Launch_ProofIsNoLongerAvailableInKeY",
                                           true,
                                           0);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}
    * that is disconnected,
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testSuspendResumeWhileDisconnected_DebugTarget_ProofIsNoLongerAvailableInKeY() throws Exception {
      doTestSuspendResumeWhileDisconnected("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeWhileDisconnected_DebugTarget_ProofIsNoLongerAvailableInKeY",
                                           true,
                                           0, 0);
   }
   
   /**
    * Executes the tests for {@link #testSuspendResumeWhileDisconnected_Launch()}
    * and {@link #testSuspendResumeWhileDisconnected_DebugTarget()}.
    * @param projectName The project name to use.
    * @param clearProofListInKeYBeforeDisconnect Clear proof list in KeY before disconnecting the {@link ILaunch}?
    * @param pathToElementInDebugTreeWhichProvidesDisconnectMenuItem The path to the element which provides the "Disconnect" menu item in the debug tree.
    * @throws Exception Occurred Exception.
    */
   protected void doTestSuspendResumeWhileDisconnected(String projectName,
                                                       final boolean clearProofListInKeYBeforeDisconnect,
                                                       final int... pathToElementInDebugTreeWhichProvidesDisconnectMenuItem) throws Exception {
      IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            // Test launch commands after loading completed
            assertTrue(launch.canTerminate());
            assertFalse(launch.isTerminated());
            assertTrue(target instanceof ISEDDebugTarget);
            assertTrue(target.canDisconnect());
            assertTrue(target.canResume());
            assertFalse(target.canSuspend());
            assertTrue(target.canTerminate());
            assertFalse(target.isDisconnected());
            assertTrue(target.isSuspended());
            assertFalse(target.isTerminated());
            // Make sure that the debug target is in the initial state.
            TestSEDKeyCoreUtil.assertInitialTarget(target, targetName);
            if (clearProofListInKeYBeforeDisconnect) {
               // Clear proof list in KeY
               assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
               KeYUtil.clearProofList(MainWindow.getInstance());
               assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
            }
            else {
               // Disconnect
               SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, pathToElementInDebugTreeWhichProvidesDisconnectMenuItem); // Select first debug target
               item.contextMenu("Disconnect").click();
            }
            assertTrue(launch instanceof IDisconnect);
            TestSedCoreUtil.waitUntilLaunchIsDisconnected(bot, (IDisconnect)launch);
            assertTrue(launch.canTerminate());
            assertTrue(launch.isTerminated()); // Also disconnected debug targets are seen as terminated by the Eclipse Debug API.
            assertTrue(target instanceof ISEDDebugTarget);
            assertFalse(target.canDisconnect());
            assertFalse(target.canResume());
            assertFalse(target.canSuspend());
            assertTrue(target.canTerminate());
            assertTrue(target.isDisconnected());
            assertTrue(target.isSuspended());
            assertFalse(target.isTerminated());
            // Resume launch directly in KeY
            if (!clearProofListInKeYBeforeDisconnect) {
               MainWindow.getInstance().getMediator().startAutoMode();
               KeYUtil.waitWhileMainWindowIsFrozen(MainWindow.getInstance());
            }
            // Test the unmodified execution tree
            if (clearProofListInKeYBeforeDisconnect) {
               TestSEDKeyCoreUtil.assertDisposedInitialTarget(target, targetName);
            }
            else {
               TestSEDKeyCoreUtil.assertInitialTarget(target, targetName);
            }
         }
      };
      doKeYDebugTargetTest(projectName, 
                           "data/statements/test", 
                           true,
                           true,
                           createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"), 
                           null,
                           null,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE, 
                           8, executor);
   }

   /**
    * Tests the termination functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testTerminationDebugTarget() throws Exception {
      doTerminationTest("SWTBotKeYDebugTargetTerminationTest_testTerminationDebugTarget", false, 0, 0);
   }

   /**
    * Tests the termination functionality on the {@link ILaunch}.
    */
   @Test
   public void testTerminationLaunch() throws Exception {
      doTerminationTest("SWTBotKeYDebugTargetTerminationTest_testTerminationLaunch", false, 0);
   }

   /**
    * Tests the termination functionality on the {@link IDebugTarget},
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testTerminationDebugTarget_ProofIsNoLongerAvailableInKeY() throws Exception {
      doTerminationTest("SWTBotKeYDebugTargetTerminationTest_testTerminationDebugTarget_ProofIsNoLongerAvailableInKeY", true, 0, 0);
   }

   /**
    * Tests the termination functionality on the {@link ILaunch},
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testTerminationLaunch_ProofIsNoLongerAvailableInKeY() throws Exception {
      doTerminationTest("SWTBotKeYDebugTargetTerminationTest_testTerminationLaunch_ProofIsNoLongerAvailableInKeY", true, 0);
   }
   
   /**
    * Executes the test for {@link #testTerminationDebugTarget()} and
    * {@link #testTerminationLaunch()}.
    * @param projectName The project name to use.
    * @param clearProofListInKeYBeforeTermination Clear proof list before terminating the {@link ILaunch}?
    * @param pathToElementInDebugTreeWhichProvidesTerminateMenuItem The path to the element which provides the "Terminate" menu item in the debug tree.
    * @throws Exception Occurred Exception.
    */
   protected void doTerminationTest(String projectName,
                                    final boolean clearProofListInKeYBeforeTermination,
                                    final int... pathToElementInDebugTreeWhichProvidesTerminateMenuItem) throws Exception {
      IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            // Test launch commands after loading completed
            assertTrue(launch.canTerminate());
            assertFalse(launch.isTerminated());
            assertTrue(target instanceof ISEDDebugTarget);
            assertTrue(target.canDisconnect());
            assertTrue(target.canResume());
            assertFalse(target.canSuspend());
            assertTrue(target.canTerminate());
            assertFalse(target.isDisconnected());
            assertTrue(target.isSuspended());
            assertFalse(target.isTerminated());
            // Remove proof in KeY if required
            if (clearProofListInKeYBeforeTermination) {
               assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
               KeYUtil.clearProofList(MainWindow.getInstance());
               assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
            }
            // Terminate launch
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, pathToElementInDebugTreeWhichProvidesTerminateMenuItem); // Select first launch
            item.contextMenu("Terminate").click();
            TestSedCoreUtil.waitUntilLaunchIsTerminated(bot, launch);
            assertFalse(launch.canTerminate());
            assertTrue(launch.isTerminated());
            assertFalse(target.canDisconnect());
            assertFalse(target.canResume());
            assertFalse(target.canSuspend());
            assertFalse(target.canTerminate());
            assertEquals(clearProofListInKeYBeforeTermination, target.isDisconnected());
            assertTrue(target.isSuspended());
            assertTrue(target.isTerminated());
            // Remove terminated launch
            TestUtilsUtil.clickContextMenu(debugTree, "Remove All Terminated");
            assertEquals(0, debugTree.getAllItems().length);
         }
      };
      doKeYDebugTargetTest(projectName, 
                           "data/statements/test", 
                           true,
                           true,
                           createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"), 
                           null,
                           null,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE, 
                           8, executor);
   }
}