// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * <p>
 * Tests for {@link SymbolicExecutionTreeBuilder},
 * {@link ExecutedSymbolicExecutionTreeNodesStopCondition} and
 * {@link SymbolicExecutionGoalChooser}.
 * </p>
 * <p>
 * This test needs access to the checkout of the KeY repository defined
 * via Java System Property {@code key.home}, e.g. via VM argument:
 * {@code -Dkey.home=D:\Forschung\GIT\KeY}
 * </p>
 * @author Martin Hentschel
 */
public class TestSymbolicExecutionTreeBuilder extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests example: examples/_testcase/set/useOperationContractApplyContractTwice
    */
   public void testUseOperationContractApplyContractTwice() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractApplyContractTwice/test/OperationContractAppliedTwiceTest.java", 
                "OperationContractAppliedTwiceTest", 
                "doubleMagic", 
                null,
                "examples/_testcase/set/useOperationContractApplyContractTwice/oracle/OperationContractAppliedTwiceTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/verificationProofFile_VerifyNumber
    */
   public void testVerifyNumberNormal() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/verificationProofFile_VerifyNumber/test/VerifyNumberNormal.proof",
                "examples/_testcase/set/verificationProofFile_VerifyNumber/oracle/VerifyNumberNormal.xml",
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
    * Tests example: examples/_testcase/set/verificationProofFile_VerifyMin
    */
   public void testVerifyMinTrueBranch() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/verificationProofFile_VerifyMin/test/VerifyMinTrueBranch.proof",
                "examples/_testcase/set/verificationProofFile_VerifyMin/oracle/VerifyMinTrueBranch.xml",
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
    * Tests example: examples/_testcase/set/verificationProofFile_VerifyMin
    */
   public void testVerifyMin() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/verificationProofFile_VerifyMin/test/VerifyMin.proof",
                "examples/_testcase/set/verificationProofFile_VerifyMin/oracle/VerifyMin.xml",
                true,
                true,
                true,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleMethodCallStackTest
    */
   public void testSimpleMethodCallStack() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/simpleMethodCallStackTest/test/SimpleMethodCallStackTest.java",
                "SimpleMethodCallStackTest",
                "magic",
                null,
                "examples/_testcase/set/simpleMethodCallStackTest/oracle/SimpleMethodCallStackTest.xml",
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallStackTest
    */
   public void testMethodCallStack() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/methodCallStackTest/test/MethodCallStackTest.java",
                "MethodCallStackTest",
                "magic",
                null,
                "examples/_testcase/set/methodCallStackTest/oracle/MethodCallStackTest.xml",
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/unicodeTest
    */
   public void testUnicode_Disabled() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/unicodeTest/test/UnicodeTest.java",
                "UnicodeTest",
                "magic",
                null,
                "examples/_testcase/set/unicodeTest/oracle/UnicodeTest_Disabled.xml",
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                true);
   }
   
   /**
    * Tests example: examples/_testcase/set/unicodeTest
    */
   public void testUnicode_Enabled() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/unicodeTest/test/UnicodeTest.java",
                "UnicodeTest",
                "magic",
                null,
                "examples/_testcase/set/unicodeTest/oracle/UnicodeTest_Enabled.xml",
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                true,
                true);
   }
   
   /**
    * Tests example: examples/_testcase/set/prettyPrint
    */
   public void testPrettyPrinting_Disabled() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/prettyPrint/test/PrettyPrintTest.java",
                "PrettyPrintTest",
                "main",
                null,
                "examples/_testcase/set/prettyPrint/oracle/PrettyPrintTest_Disabled.xml",
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/prettyPrint
    */
   public void testPrettyPrinting_Enabled() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/prettyPrint/test/PrettyPrintTest.java",
                "PrettyPrintTest",
                "main",
                null,
                "examples/_testcase/set/prettyPrint/oracle/PrettyPrintTest_Enabled.xml",
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                true);
   }
   
   /**
    * Tests example: examples/_testcase/set/useLoopInvariantAndOperationContractStrictlyPure
    */
   public void testLoopInvariantAndOperationContractStrictlyPure() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/useLoopInvariantAndOperationContractStrictlyPure/test/IndexOf.java",
                "IndexOf",
                "indexOf",
                null,
                "examples/_testcase/set/useLoopInvariantAndOperationContractStrictlyPure/oracle/IndexOf.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false);
   }

   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainVoidMethod() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainVoidMethod", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainVoidMethod.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainNoArgs() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainNoArgs", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainNoArgs.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainResult() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainResult", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainResult.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainResultNotSpecified() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainResultNotSpecified", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainResultNotSpecified.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainExceptinalVoid() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainExceptinalVoid", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainExceptinalVoid.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainExceptinalUnused() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainExceptinalUnused", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainExceptinalUnused.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainExceptinal() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainExceptinal", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainExceptinal.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainBooleanResultUnused() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainBooleanResultUnused", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainBooleanResultUnused.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainBooleanResultUnspecifiedUnused() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainBooleanResultUnspecifiedUnused", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainBooleanResultUnspecifiedUnused.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainExceptionalConstructor() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainExceptionalConstructor", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainExceptionalConstructor.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainConstructor() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainConstructor", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainConstructor.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/instanceContractTest
    */
   public void testInstanceContractTest_mainOnObject() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainOnObject", 
                null,
                "examples/_testcase/set/instanceContractTest/oracle/InstanceContractTest_mainOnObject.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainVoidMethod() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainVoidMethod", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainVoidMethod.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainNoArgs() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainNoArgs", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainNoArgs.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainResult() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainResult", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainResult.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainResultNotSpecified() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainResultNotSpecified", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainResultNotSpecified.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainExceptinalVoid() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainExceptinalVoid", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainExceptinalVoid.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainExceptinalUnused() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainExceptinalUnused", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainExceptinalUnused.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainExceptinal() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainExceptinal", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainExceptinal.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainBooleanResultUnused() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainBooleanResultUnused", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainBooleanResultUnused.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainBooleanResultUnspecifiedUnused() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainBooleanResultUnspecifiedUnused", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainBooleanResultUnspecifiedUnused.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainExceptionalConstructor() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainExceptionalConstructor", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainExceptionalConstructor.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainConstructor() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainConstructor", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainConstructor.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticContractTest
    */
   public void testStaticContractTest_mainOnObject() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainOnObject", 
                null,
                "examples/_testcase/set/staticContractTest/oracle/StaticContractTest_mainOnObject.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/verifiedTest
    */
   public void testVerifiedTest_notLoop() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::notLoop(int)].JML operation contract.0", 
                "examples/_testcase/set/verifiedTest/oracle/VerifiedTest_notLoop.xml",
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }

   /**
    * Tests example: examples/_testcase/set/verifiedTest
    */
   public void testVerifiedTest_loop() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::loop(int)].JML operation contract.0", 
                "examples/_testcase/set/verifiedTest/oracle/VerifiedTest_loop.xml",
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }

   /**
    * Tests example: examples/_testcase/set/verifiedTest
    */
   public void testVerifiedTest_notMagic() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::notMagic()].JML operation contract.0", 
                "examples/_testcase/set/verifiedTest/oracle/VerifiedTest_notMagic.xml",
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }

   /**
    * Tests example: examples/_testcase/set/verifiedTest
    */
   public void testVerifiedTest_magic() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::magic()].JML operation contract.0", 
                "examples/_testcase/set/verifiedTest/oracle/VerifiedTest_magic.xml",
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/verifiedTest
    */
   public void testVerifiedTest_notMagicException() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::notMagicException()].JML exceptional_behavior operation contract.0", 
                "examples/_testcase/set/verifiedTest/oracle/VerifiedTest_notMagicException.xml",
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/verifiedTest
    */
   public void testVerifiedTest_magicException() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::magicException()].JML exceptional_behavior operation contract.0", 
                "examples/_testcase/set/verifiedTest/oracle/VerifiedTest_magicException.xml",
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallReturnTests
    */
   public void testMethodCallReturnTests() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodCallReturnTests/test/MethodCallReturnTests.java", 
                "MethodCallReturnTests", 
                "main", 
                null,
                "examples/_testcase/set/methodCallReturnTests/oracle/MethodCallReturnTests.xml",
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useLoopInvariantArrayAverage
    */
   public void testUseLoopInvariantArrayAverage() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArrayAverage/test/ArrayAverage.java", 
                "ArrayAverage", 
                "average", 
                null,
                "examples/_testcase/set/useLoopInvariantArrayAverage/oracle/ArrayAverage.xml",
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractStatementsInImpliciteConstructor
    */
   public void testUseOperationContractStatementsInImpliciteConstructor() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractStatementsInImpliciteConstructor/test/UseOperationContractStatementsInImpliciteConstructor.java", 
                "UseOperationContractStatementsInImpliciteConstructor", 
                "average", 
                null,
                "examples/_testcase/set/useOperationContractStatementsInImpliciteConstructor/oracle/UseOperationContractStatementsInImpliciteConstructor.xml",
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantLoopSplittingCondition
    * </p>
    * <p>
    * Tests the handling of method returns in different modalities.
    * </p>
    */
   public void testUseLoopInvariantLoopSplittingCondition() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantLoopSplittingCondition/test/LoopSplittingCondition.java", 
                "LoopSplittingCondition", 
                "main", 
                null,
                "examples/_testcase/set/useLoopInvariantLoopSplittingCondition/oracle/LoopSplittingCondition.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantTwoLoops
    * </p>
    * <p>
    * Tests the handling of method returns in different modalities.
    * </p>
    */
   public void testUseLoopInvariantTwoLoops() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantTwoLoops/test/TwoLoops.java", 
                "TwoLoops", 
                "main", 
                null,
                "examples/_testcase/set/useLoopInvariantTwoLoops/oracle/TwoLoops.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsConditionFullImplemented
    * </p>
    * <p>
    * Tests the handling of method returns in different modalities.
    * </p>
    */
   public void testLoopInvariantMethodReturnInDifferentModalities() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsConditionFullImplemented/test/WhileWithMethodCallAsConditionFullImplemented.java", 
                "WhileWithMethodCallAsConditionFullImplemented", 
                "size", 
                null,
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsConditionFullImplemented/oracle/WhileWithMethodCallAsConditionFullImplemented.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantLoopBodyBranchClosed
    * </p>
    * <p>
    * Tests the handling of {@code continue} when a loop is expanded.
    * </p>
    */
   public void testLoopBodyBranchClosed() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantLoopBodyBranchClosed/test/LoopBodyBranchClosed.java", 
                "LoopBodyBranchClosed", 
                "deadBody", 
                null,
                "examples/_testcase/set/useLoopInvariantLoopBodyBranchClosed/oracle/LoopBodyBranchClosed.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantLoopUsageBranchClosed
    * </p>
    * <p>
    * Tests the handling of {@code continue} when a loop is expanded.
    * </p>
    */
   public void testLoopUsageBranchClosed() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantLoopUsageBranchClosed/test/LoopUsageBranchClosed.java", 
                "LoopUsageBranchClosed", 
                "deadCodeAfterLoop", 
                null,
                "examples/_testcase/set/useLoopInvariantLoopUsageBranchClosed/oracle/LoopUsageBranchClosed.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/nestedLoopsWithContinue
    * </p>
    * <p>
    * Tests the handling of {@code continue} when a loop is expanded.
    * </p>
    */
   public void testNestedLoopsWithContinue() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/nestedLoopsWithContinue/test/NestedLoopsWithContinue.java", 
                "NestedLoopsWithContinue", 
                "main", 
                null,
                "examples/_testcase/set/nestedLoopsWithContinue/oracle/NestedLoopsWithContinue.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumWhileWithContinue
    * </p>
    * <p>
    * Tests the handling of {@code continue} when a loop invariant is applied.
    * </p>
    */
   public void testArraySumWhileWithContinue() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArraySumWhileWithContinue/test/ArraySumWhileWithContinue.java", 
                "ArraySumWhileWithContinue", 
                "sum", 
                null,
                "examples/_testcase/set/useLoopInvariantArraySumWhileWithContinue/oracle/ArraySumWhileWithContinue.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantVoidWhileWithReturn
    * </p>
    * <p>
    * Tests the handling of {@code return} when a loop invariant is applied.
    * </p>
    */
   public void testVoidWhileWithReturn() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantVoidWhileWithReturn/test/VoidWhileWithReturn.java", 
                "VoidWhileWithReturn", 
                "sum", 
                null,
                "examples/_testcase/set/useLoopInvariantVoidWhileWithReturn/oracle/VoidWhileWithReturn.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumWhileWithReturn
    * </p>
    * <p>
    * Tests the handling of {@code return} when a loop invariant is applied.
    * </p>
    */
   public void testArraySumWhileWithReturn() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArraySumWhileWithReturn/test/ArraySumWhileWithReturn.java", 
                "ArraySumWhileWithReturn", 
                "sum", 
                null,
                "examples/_testcase/set/useLoopInvariantArraySumWhileWithReturn/oracle/ArraySumWhileWithReturn.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumWhileWithBreak
    * </p>
    * <p>
    * Tests the handling of {@code break} when a loop invariant is applied.
    * </p>
    */
   public void testArraySumWhileWithBreak() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArraySumWhileWithBreak/test/ArraySumWhileWithBreak.java", 
                "ArraySumWhileWithBreak", 
                "sum", 
                null,
                "examples/_testcase/set/useLoopInvariantArraySumWhileWithBreak/oracle/ArraySumWhileWithBreak.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumWhileWithException
    * </p>
    * <p>
    * Tests the handling of thrown exceptions when a loop invariant is applied.
    * </p>
    */
   public void testArraySumWhileWithException() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArraySumWhileWithException/test/ArraySumWhileWithException.java", 
                "ArraySumWhileWithException", 
                "sum", 
                "array != null",
                "examples/_testcase/set/useLoopInvariantArraySumWhileWithException/oracle/ArraySumWhileWithException.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithMethodCallAsCondition_preMethodContract() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition/test/WhileWithMethodCallAsCondition.java", 
                "WhileWithMethodCallAsCondition", 
                "size", 
                "array != null",
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition/oracle/WhileWithMethodCallAsCondition_preMethodContract.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithMethodCallAsCondition_preExpandMethods() throws Exception {
      doSETTest(keyRepDirectory,
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition/test/WhileWithMethodCallAsCondition.java", 
                "WhileWithMethodCallAsCondition", 
                "size", 
                "array != null",
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition/oracle/WhileWithMethodCallAsCondition_preExpandMethods.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithMethodCallAsCondition_NoPreMethodContract() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition/test/WhileWithMethodCallAsCondition.java", 
                "WhileWithMethodCallAsCondition", 
                "size", 
                null,
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition/oracle/WhileWithMethodCallAsCondition_NoPreMethodContract.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantWhileWithLoopInvariantInCondition
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithLoopInvariantInCondition() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantWhileWithLoopInvariantInCondition/test/WhileWithLoopInvariantInCondition.java", 
                "WhileWithLoopInvariantInCondition", 
                "size", 
                null,
                "examples/_testcase/set/useLoopInvariantWhileWithLoopInvariantInCondition/oracle/WhileWithLoopInvariantInCondition.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsConditionOnObject
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithMethodCallAsConditionOnObject() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsConditionOnObject/test/WhileWithMethodCallAsConditionOnObject.java", 
                "WhileWithMethodCallAsConditionOnObject", 
                "size", 
                null,
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsConditionOnObject/oracle/WhileWithMethodCallAsConditionOnObject.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithMethodCallAsCondition_NoPreExpandMethods() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition/test/WhileWithMethodCallAsCondition.java", 
                "WhileWithMethodCallAsCondition", 
                "size", 
                null,
                "examples/_testcase/set/useLoopInvariantWhileWithMethodCallAsCondition/oracle/WhileWithMethodCallAsCondition_NoPreExpandMethods.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantArraySizeDoWhile
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySizeDoWhile() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArraySizeDoWhile/test/ArraySizeDoWhile.java", 
                "ArraySizeDoWhile", 
                "size", 
                "array != null",
                "examples/_testcase/set/useLoopInvariantArraySizeDoWhile/oracle/ArraySizeDoWhile.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantArraySizeWhile
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySizeWhile() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArraySizeWhile/test/ArraySizeWhile.java", 
                "ArraySizeWhile", 
                "size", 
                "array != null",
                "examples/_testcase/set/useLoopInvariantArraySizeWhile/oracle/ArraySizeWhile.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumFor
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySumFor() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArraySumFor/test/ArraySumFor.java", 
                "ArraySumFor", 
                "sum", 
                "array != null",
                "examples/_testcase/set/useLoopInvariantArraySumFor/oracle/ArraySumFor.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumForEach
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySumForEach() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArraySumForEach/test/ArraySumForEach.java", 
                "ArraySumForEach", 
                "sum", 
                "array != null",
                "examples/_testcase/set/useLoopInvariantArraySumForEach/oracle/ArraySumForEach.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumWhile
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySumWhile() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArraySumWhile/test/ArraySumWhile.java", 
                "ArraySumWhile", 
                "sum", 
                "array != null",
                "examples/_testcase/set/useLoopInvariantArraySumWhile/oracle/ArraySumWhile.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumWhileInitiallyInvalid
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySumWhileInitiallyInvalid() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useLoopInvariantArraySumWhileInitiallyInvalid/test/ArraySumWhileInitiallyInvalid.java", 
                "ArraySumWhileInitiallyInvalid", 
                "sum", 
                "array != null",
                "examples/_testcase/set/useLoopInvariantArraySumWhileInitiallyInvalid/oracle/ArraySumWhileInitiallyInvalid.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractQueryTest
    */
   public void testUseOperationContractQueryTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractQueryTest/test/UseOperationContractQueryTest.java", 
                "UseOperationContractQueryTest", 
                "main", 
                "value == magicNumber()",
                "examples/_testcase/set/useOperationContractQueryTest/oracle/UseOperationContractQueryTest.xml",
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractAllBranchesOpenTest
    */
   public void testUseOperationContractAllBranchesOpenTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractAllBranchesOpenTest/test/UseOperationContractAllBranchesOpenTest.java", 
                "UseOperationContractAllBranchesOpenTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractAllBranchesOpenTest/oracle/UseOperationContractAllBranchesOpenTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/identicalTermsDuringProof
    */
   public void testIdenticalTermsDuringProof() throws Exception {
      // Make sure that correct symbolic execution tree is created.
      SymbolicExecutionEnvironment<CustomUserInterface> env = doSETTest(keyRepDirectory, 
                                                                               "examples/_testcase/set/identicalTermsDuringProof/test/IdenticalTermsDuringProof.java", 
                                                                               "IdenticalTermsDuringProof", 
                                                                               "mid", 
                                                                               null,
                                                                               "examples/_testcase/set/identicalTermsDuringProof/oracle/IdenticalTermsDuringProof.xml",
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               ALL_IN_ONE_RUN,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false);
      try {
         // Find both statements "mid = y;".
         IExecutionStart startNode = env.getBuilder().getStartNode();
         IExecutionMethodCall methodCall = (IExecutionMethodCall)startNode.getChildren()[0];
         IExecutionStatement intMidZ = (IExecutionStatement)methodCall.getChildren()[0];
         IExecutionBranchStatement ifYZ = (IExecutionBranchStatement)intMidZ.getChildren()[0];
         IExecutionBranchCondition notXY = (IExecutionBranchCondition)ifYZ.getChildren()[0];
         IExecutionBranchStatement ifXZ = (IExecutionBranchStatement)notXY.getChildren()[0];
         IExecutionBranchCondition not1X = (IExecutionBranchCondition)ifXZ.getChildren()[0];
         IExecutionStatement midThenBranch = (IExecutionStatement)not1X.getChildren()[0];
         IExecutionBranchCondition not1Y = (IExecutionBranchCondition)ifYZ.getChildren()[1];
         IExecutionStatement midElseBranch = (IExecutionStatement)not1Y.getChildren()[0];
         // Make sure that both statements "mid = y;" have the correct position info.
         assertNotSame(midThenBranch, midElseBranch);
         assertNotSame(midThenBranch.getActiveStatement(), midElseBranch.getActiveStatement());
         PositionInfo thenPosition = midThenBranch.getActivePositionInfo();
         PositionInfo elsePosition = midElseBranch.getActivePositionInfo();
         assertNotSame(thenPosition, elsePosition);
         assertNotSame(PositionInfo.UNDEFINED, thenPosition);
         assertNotSame(PositionInfo.UNDEFINED, elsePosition);
         assertEquals(6, thenPosition.getStartPosition().getLine());
         assertEquals(21, thenPosition.getStartPosition().getColumn());
         assertEquals(6, thenPosition.getEndPosition().getLine());
         assertEquals(24, thenPosition.getEndPosition().getColumn());
         assertEquals(9, elsePosition.getStartPosition().getLine());
         assertEquals(17, elsePosition.getStartPosition().getColumn());
         assertEquals(9, elsePosition.getEndPosition().getLine());
         assertEquals(20, elsePosition.getEndPosition().getColumn());
      }
      finally {
         env.dispose();
      }
   }
   
   /**
    * Tests example: examples/_testcase/set/labelTest
    */
   public void testLabelTest_doubled() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/labelTest/test/LabelTest.java", 
                "LabelTest", 
                "doubled", 
                null,
                "examples/_testcase/set/labelTest/oracle/LabelTest_doubled.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/labelTest
    */
   public void testLabelTest_lost() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/labelTest/test/LabelTest.java", 
                "LabelTest", 
                "lost", 
                null,
                "examples/_testcase/set/labelTest/oracle/LabelTest_lost.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/emptyBlockTest
    */
   public void testEmptyBlockTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/emptyBlockTest/test/EmptyBlockTest.java", 
                "EmptyBlockTest", 
                "emptyBlocks", 
                null,
                "examples/_testcase/set/emptyBlockTest/oracle/EmptyBlockTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractExceptionalNoPreconditionWithNullCheckTest
    */
   public void testUseOperationContractExceptionalNoPreconditionWithNullCheckTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractExceptionalNoPreconditionWithNullCheckTest/test/UseOperationContractExceptionalNoPreconditionWithNullCheckTest.java", 
                "UseOperationContractExceptionalNoPreconditionWithNullCheckTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractExceptionalNoPreconditionWithNullCheckTest/oracle/UseOperationContractExceptionalNoPreconditionWithNullCheckTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractFalsePreconditionTest
    */
   public void testUseOperationContractFalsePreconditionTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractFalsePreconditionTest/test/UseOperationContractFalsePreconditionTest.java", 
                "UseOperationContractFalsePreconditionTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractFalsePreconditionTest/oracle/UseOperationContractFalsePreconditionTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractFixedNormalPostTest
    */
   public void testUseOperationContractFixedNormalPostTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractFixedNormalPostTest/test/UseOperationContractFixedNormalPostTest.java", 
                "UseOperationContractFixedNormalPostTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractFixedNormalPostTest/oracle/UseOperationContractFixedNormalPostTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractInvalidPreconditionOnObjectTest
    */
   public void testUseOperationContractInvalidPreconditionOnObjectTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractInvalidPreconditionOnObjectTest/test/UseOperationContractInvalidPreconditionOnObjectTest.java", 
                "UseOperationContractInvalidPreconditionOnObjectTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractInvalidPreconditionOnObjectTest/oracle/UseOperationContractInvalidPreconditionOnObjectTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractInvalidPreconditionTest
    */
   public void testUseOperationContractInvalidPreconditionTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractInvalidPreconditionTest/test/UseOperationContractInvalidPreconditionTest.java", 
                "UseOperationContractInvalidPreconditionTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractInvalidPreconditionTest/oracle/UseOperationContractInvalidPreconditionTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractNoExceptionTest
    */
   public void testUseOperationContractNoExceptionTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractNoExceptionTest/test/UseOperationContractNoExceptionTest.java", 
                "UseOperationContractNoExceptionTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractNoExceptionTest/oracle/UseOperationContractNoExceptionTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractNoPreconditionTest
    */
   public void testUseOperationContractNoPreconditionTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractNoPreconditionTest/test/UseOperationContractNoPreconditionTest.java", 
                "UseOperationContractNoPreconditionTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractNoPreconditionTest/oracle/UseOperationContractNoPreconditionTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractNoPreconditionWithNullCheckTest
    */
   public void testUseOperationContractNoPreconditionWithNullCheckTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractNoPreconditionWithNullCheckTest/test/UseOperationContractNoPreconditionWithNullCheckTest.java", 
                "UseOperationContractNoPreconditionWithNullCheckTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractNoPreconditionWithNullCheckTest/oracle/UseOperationContractNoPreconditionWithNullCheckTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractNormalAndExceptionalBranchTest
    */
   public void testUseOperationContractNormalAndExceptionalBranchTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractNormalAndExceptionalBranchTest/test/UseOperationContractNormalAndExceptionalBranchTest.java", 
                "UseOperationContractNormalAndExceptionalBranchTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractNormalAndExceptionalBranchTest/oracle/UseOperationContractNormalAndExceptionalBranchTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractNormalAndExceptionalTogetherTest
    */
   public void testUseOperationContractNormalAndExceptionalTogetherTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractNormalAndExceptionalTogetherTest/test/UseOperationContractNormalAndExceptionalTogetherTest.java", 
                "UseOperationContractNormalAndExceptionalTogetherTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractNormalAndExceptionalTogetherTest/oracle/UseOperationContractNormalAndExceptionalTogetherTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/complexConstructorTest
    */
   public void testComplexConstructorTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/complexConstructorTest/test/ComplexConstructorTest.java", 
                "ComplexConstructorTest", 
                "main", 
                null,
                "examples/_testcase/set/complexConstructorTest/oracle/ComplexConstructorTest.xml",
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleConstructorTest
    */
   public void testSimpleConstructorTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/simpleConstructorTest/test/SimpleConstructorTest.java", 
                "SimpleConstructorTest", 
                "main", 
                null,
                "examples/_testcase/set/simpleConstructorTest/oracle/SimpleConstructorTest.xml",
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesUnknownTest
    */
   public void testVariablesUnknownTest() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/variablesUnknownTest/test/UnknownTest.java", 
                          "endless.UnknownTest",
                          "main", 
                          null,
                          "examples/_testcase/set/variablesUnknownTest/oracle/UnknownTest.xml",
                          true,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesParameterAttributesChange
    */
   public void testElseIfTest_variablesParameterAttributesChange() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/variablesParameterAttributesChange/test/VariablesParameterAttributesChange.java", 
                "VariablesParameterAttributesChange", 
                "main", 
                null,
                "examples/_testcase/set/variablesParameterAttributesChange/oracle/VariablesParameterAttributesChange.xml",
                true,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/elseIfTest
    */
   public void testElseIfTest_mergedBranchConditions() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/elseIfTest/test/ElseIfTest.java", 
                "ElseIfTest", 
                "elseIf", 
                null,
                "examples/_testcase/set/elseIfTest/oracle/ElseIfTestMergedBranchConditions.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/switchCaseTest
    */
   public void testSwitchCaseTest_mergedBranchConditions() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/switchCaseTest/test/SwitchCaseTest.java", 
                "SwitchCaseTest", 
                "switchCase", 
                null,
                "examples/_testcase/set/switchCaseTest/oracle/SwitchCaseTestMergedBranchConditions.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/loopIterationTest
    */
   public void testLoopIteration_LoopWithMethod() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/loopIterationTest/test/LoopIterationTest.java", 
                "LoopIterationTest", 
                "loopMultipleTimes", 
                null,
                "examples/_testcase/set/loopIterationTest/oracle/LoopIterationTest_loopMultipleTimes.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/loopIterationTest
    */
   public void testLoopIteration_LoopStatementCopied() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/loopIterationTest/test/LoopIterationTest.java", 
                "LoopIterationTest", 
                "mainWorks", 
                null,
                "examples/_testcase/set/loopIterationTest/oracle/LoopIterationTest_mainWorks.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/loopIterationTest
    */
   public void testLoopIteration_LoopStatementReused() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/loopIterationTest/test/LoopIterationTest.java", 
                "LoopIterationTest", 
                "main", 
                null,
                "examples/_testcase/set/loopIterationTest/oracle/LoopIterationTest_main.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesArrayTest
    */
   public void testVariablesArrayTest() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/variablesArrayTest/test/VariablesArrayTest.java", 
                          "VariablesArrayTest", 
                          "main", 
                          null,
                          "examples/_testcase/set/variablesArrayTest/oracle/VariablesArrayTest.xml",
                          true,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesInstanceVariableTest
    */
   public void testVariablesInstanceVariableTest() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/variablesInstanceVariableTest/test/VariablesInstanceVariableTest.java", 
                          "VariablesInstanceVariableTest", 
                          "main", 
                          null,
                          "examples/_testcase/set/variablesInstanceVariableTest/oracle/VariablesInstanceVariableTest.xml",
                          true,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesLocalTest
    */
   public void testVariablesLocalTest() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/variablesLocalTest/test/VariablesLocalTest.java", 
                          "VariablesLocalTest", 
                          "main", 
                          null,
                          "examples/_testcase/set/variablesLocalTest/oracle/VariablesLocalTest.xml",
                          true,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesStaticTest
    */
   public void testVariablesStaticTest() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/variablesStaticTest/test/VariablesStaticTest.java", 
                          "VariablesStaticTest", 
                          "main", 
                          null,
                          "examples/_testcase/set/variablesStaticTest/oracle/VariablesStaticTest.xml",
                          true,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/complexFlatSteps
    */
   public void testComplexFlatSteps() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/complexFlatSteps/test/ComplexFlatSteps.java", 
                "ComplexFlatSteps", 
                "doSomething", 
                null,
                "examples/_testcase/set/complexFlatSteps/oracle/ComplexFlatSteps.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/complexIf
    */
   public void testComplexIf() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/complexIf/test/ComplexIf.java", 
                "ComplexIf", 
                "min", 
                null,
                "examples/_testcase/set/complexIf/oracle/ComplexIf.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/doWhileFalseTest
    */
   public void testDoWhileFlaseTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/doWhileFalseTest/test/DoWhileFalseTest.java", 
                "DoWhileFalseTest", 
                "main", 
                null,
                "examples/_testcase/set/doWhileFalseTest/oracle/DoWhileFalseTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/doWhileTest
    */
   public void testDoWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/doWhileTest/test/DoWhileTest.java", 
                "DoWhileTest", 
                "main", 
                null,
                "examples/_testcase/set/doWhileTest/oracle/DoWhileTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/elseIfDifferentVariables
    */
   public void testElseIfDifferentVariables() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/elseIfDifferentVariables/test/ElseIfDifferentVariables.java", 
                "ElseIfDifferentVariables", 
                "main", 
                null,
                "examples/_testcase/set/elseIfDifferentVariables/oracle/ElseIfDifferentVariables.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/elseIfTest
    */
   public void testElseIfTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/elseIfTest/test/ElseIfTest.java", 
                "ElseIfTest", 
                "elseIf", 
                null,
                "examples/_testcase/set/elseIfTest/oracle/ElseIfTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/fixedRecursiveMethodCallTest
    */
   public void testFixedRecursiveMethodCallTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/fixedRecursiveMethodCallTest/test/FixedRecursiveMethodCallTest.java", 
                "FixedRecursiveMethodCallTest", 
                "decreaseValue", 
                null,
                "examples/_testcase/set/fixedRecursiveMethodCallTest/oracle/FixedRecursiveMethodCallTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/forEachTest
    */
   public void testForEachTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/forEachTest/test/ForEachTest.java", 
                "ForEachTest", 
                "main", 
                null,
                "examples/_testcase/set/forEachTest/oracle/ForEachTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/forFalseTest
    */
   public void testForFalseTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/forFalseTest/test/ForFalseTest.java", 
                "ForFalseTest", 
                "main", 
                null,
                "examples/_testcase/set/forFalseTest/oracle/ForFalseTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/forTest
    */
   public void testForTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/forTest/test/ForTest.java", 
                "ForTest", 
                "main", 
                null,
                "examples/_testcase/set/forTest/oracle/ForTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalDoWhileTest
    */
   public void testFunctionalDoWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/functionalDoWhileTest/test/FunctionalDoWhileTest.java", 
                "FunctionalDoWhileTest", 
                "main", 
                null,
                "examples/_testcase/set/functionalDoWhileTest/oracle/FunctionalDoWhileTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalForTest
    */
   public void testFunctionalForTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/functionalForTest/test/FunctionalForTest.java", 
                "FunctionalForTest", 
                "main", 
                null,
                "examples/_testcase/set/functionalForTest/oracle/FunctionalForTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalIf
    */
   public void testFunctionalIf() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/functionalIf/test/FunctionalIf.java", 
                "FunctionalIf", 
                "min", 
                null,
                "examples/_testcase/set/functionalIf/oracle/FunctionalIf.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalWhileTest
    */
   public void testFunctionalWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/functionalWhileTest/test/FunctionalWhileTest.java", 
                "FunctionalWhileTest", 
                "main", 
                null,
                "examples/_testcase/set/functionalWhileTest/oracle/FunctionalWhileTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallOnObject
    */
   public void testMethodCallOnObject() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodCallOnObject/test/MethodCallOnObject.java", 
                "MethodCallOnObject", 
                "main", 
                null,
                "examples/_testcase/set/methodCallOnObject/oracle/MethodCallOnObject.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallOnObjectWithException
    */
   public void testMethodCallOnObjectWithException() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodCallOnObjectWithException/test/MethodCallOnObjectWithException.java", 
                "MethodCallOnObjectWithException", 
                "main", 
                null,
                "examples/_testcase/set/methodCallOnObjectWithException/oracle/MethodCallOnObjectWithException.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallParallelTest
    */
   public void testMethodCallParallelTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodCallParallelTest/test/MethodCallParallelTest.java", 
                "MethodCallParallelTest", 
                "main", 
                null,
                "examples/_testcase/set/methodCallParallelTest/oracle/MethodCallParallelTest.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodFormatTest
    */
   public void testMethodFormatTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodFormatTest/test/MethodFormatTest.java", 
                "MethodFormatTest", 
                "main", 
                null,
                "examples/_testcase/set/methodFormatTest/oracle/MethodFormatTest.xml",
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodHierarchyCallTest
    */
   public void testMethodHierarchyCallTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodHierarchyCallTest/test/MethodHierarchyCallTest.java", 
                "MethodHierarchyCallTest", 
                "main", 
                null,
                "examples/_testcase/set/methodHierarchyCallTest/oracle/MethodHierarchyCallTest.xml",
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodHierarchyCallWithExceptionTest
    */
   public void testMethodHierarchyCallWithExceptionTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodHierarchyCallWithExceptionTest/test/MethodHierarchyCallWithExceptionTest.java", 
                "MethodHierarchyCallWithExceptionTest", 
                "main", 
                null,
                "examples/_testcase/set/methodHierarchyCallWithExceptionTest/oracle/MethodHierarchyCallWithExceptionTest.xml",
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedDoWhileTest
    */
   public void testNestedDoWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/nestedDoWhileTest/test/NestedDoWhileTest.java", 
                "NestedDoWhileTest", 
                "main", 
                null,
                "examples/_testcase/set/nestedDoWhileTest/oracle/NestedDoWhileTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedForTest
    */
   public void testNestedForTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/nestedForTest/test/NestedForTest.java", 
                "NestedForTest", 
                "main", 
                null,
                "examples/_testcase/set/nestedForTest/oracle/NestedForTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedWhileTest
    */
   public void testNestedWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/nestedWhileTest/test/NestedWhileTest.java", 
                "NestedWhileTest", 
                "mainNested", 
                 null,
                "examples/_testcase/set/nestedWhileTest/oracle/NestedWhileTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/recursiveFibonacci
    * </p>
    * <p>
    * This test produces a deep symbolic execution tree to make sure
    * that no {@link StackOverflowError}s are thrown.
    * </p>
    */
   public void testRecursiveFibonacci_LONG_RUNNING_TEST() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/recursiveFibonacci/test/RecursiveFibonacci.java", 
                          "RecursiveFibonacci", 
                          "fibonacci10", 
                          null,
                          "examples/_testcase/set/recursiveFibonacci/oracle/RecursiveFibonacci.xml",
                          false,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleIf
    */
   public void testSimpleIf() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/simpleIf/test/SimpleIf.java", 
                "SimpleIf", 
                "min", 
                null,
                "examples/_testcase/set/simpleIf/oracle/SimpleIf.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleNullPointerSplitTest
    */
   public void testSimpleNullPointerSplitTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/simpleNullPointerSplitTest/test/SimpleNullPointerSplitTest.java", 
                "SimpleNullPointerSplitTest", 
                "main", 
                null,
                "examples/_testcase/set/simpleNullPointerSplitTest/oracle/SimpleNullPointerSplitTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/statementKindTest
    */
   public void testStatementKindTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/statementKindTest/test/StatementKindTest.java", 
                "StatementKindTest", 
                "main", 
                null,
                "examples/_testcase/set/statementKindTest/oracle/StatementKindTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/statements
    */
   public void testStatements() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/statements/test/FlatSteps.java", 
                "FlatSteps", 
                "doSomething", 
                null,
                "examples/_testcase/set/statements/oracle/FlatSteps.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticMethodCall
    */
   public void testStaticMethodCall() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticMethodCall/test/StaticMethodCall.java", 
                "StaticMethodCall", 
                "main", 
                null,
                "examples/_testcase/set/staticMethodCall/oracle/StaticMethodCall.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/switchCaseTest
    */
   public void testSwitchCaseTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/switchCaseTest/test/SwitchCaseTest.java", 
                "SwitchCaseTest", 
                "switchCase", 
                null,
                "examples/_testcase/set/switchCaseTest/oracle/SwitchCaseTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/throwTest
    */
   public void testThrowTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/throwTest/test/ThrowTest.java", 
                "ThrowTest", 
                "main", 
                null,
                "examples/_testcase/set/throwTest/oracle/ThrowTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/throwVariableTest
    */
   public void testThrowVariableTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/throwVariableTest/test/ThrowVariableTest.java", 
                "ThrowVariableTest", 
                "main", 
                null,
                "examples/_testcase/set/throwVariableTest/oracle/ThrowVariableTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/tryCatchFinally
    */
   public void testTryCatchFinally() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/tryCatchFinally/test/TryCatchFinally.java", 
                "TryCatchFinally", 
                "tryCatchFinally", 
                null,
                "examples/_testcase/set/tryCatchFinally/oracle/TryCatchFinally.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/whileFalseTest
    */
   public void testWhileFalseTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/whileFalseTest/test/WhileFalseTest.java", 
                "WhileFalseTest", 
                "main", 
                null,
                "examples/_testcase/set/whileFalseTest/oracle/WhileFalseTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/whileTest
    */
   public void testWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/whileTest/test/WhileTest.java", 
                "WhileTest", 
                "main", 
                null,
                "examples/_testcase/set/whileTest/oracle/WhileTest.xml",
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
}