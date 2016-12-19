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

package de.uka.ilkd.key.symbolic_execution.testcase;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import org.junit.FixMethodOrder;
import org.junit.runners.MethodSorters;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.SymbolicLayoutExtractor;
import de.uka.ilkd.key.symbolic_execution.SymbolicLayoutReader;
import de.uka.ilkd.key.symbolic_execution.SymbolicLayoutWriter;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicState;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

/**
 * Tests {@link SymbolicLayoutExtractor}.
 * @author Martin Hentschel
 */
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class TestSymbolicLayoutExtractor extends AbstractSymbolicExecutionTestCase {
//   public void testSimpleLinkedOjbectsWithAdditionalInstances() throws Exception {
//      doTest("/set/configurationExtractorSimpleLinkedOjbectsWithAdditionalInstances/test/SimpleLinkedOjbectsWithAdditionalInstances.java",
//             "SimpleLinkedOjbectsWithAdditionalInstances",
//             "/set/configurationExtractorSimpleLinkedOjbectsWithAdditionalInstances/oracle/",
//             "SimpleLinkedOjbectsWithAdditionalInstances.xml",
//             "testSimpleLinkedOjbectsWithAdditionalInstances_initial",
//             ".xml",
//             "testSimpleLinkedOjbectsWithAdditionalInstances_current",
//             ".xml",
//             null);
//   }

//   public void testSimpleLinkedOjbectsWithAdditionalInstancesPreCondition() throws Exception {
//      doTest("/set/configurationExtractorSimpleLinkedOjbectsWithAdditionalInstances/test/SimpleLinkedOjbectsWithAdditionalInstances.java",
//             "SimpleLinkedOjbectsWithAdditionalInstances",
//             "/set/configurationExtractorSimpleLinkedOjbectsWithAdditionalInstances/oracle/",
//             "SimpleLinkedOjbectsWithAdditionalInstances.xml",
//             "testSimpleLinkedOjbectsWithAdditionalInstancesPreCondition_initial",
//             ".xml",
//             "testSimpleLinkedOjbectsWithAdditionalInstancesPreCondition_current",
//             ".xml",
//             "x != null & x.next != null & x.next.next != null & a != null & a.x == 42 & b != null");
//   }

   /**
    * Tests "configurationExtractorInstanceCreationTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testEmptyArrayCreationTest() throws Exception {
      doTest("/set/configurationExtractorEmptyArrayCreationTest/test/EmptyArrayCreationTest.java",
             "EmptyArrayCreationTest",
             "/set/configurationExtractorEmptyArrayCreationTest/oracle/",
             "EmptyArrayCreationTest.xml",
             "testEmptyArrayCreationTest_initial",
             ".xml",
             "testEmptyArrayCreationTest_current",
             ".xml",
             "n == 0",
             1,
             1,
             false,
             false);
   }
      
   /**
    * Tests "configurationExtractorInstanceCreationTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testArrayCreationTest() throws Exception {
      doTest("/set/configurationExtractorArrayCreationTest/test/ArrayCreationTest.java",
             "ArrayCreationTest",
             "/set/configurationExtractorArrayCreationTest/oracle/",
             "ArrayCreationTest.xml",
             "testArrayCreationTest_initial",
             ".xml",
             "testArrayCreationTest_current",
             ".xml",
             "n >= 4",
             1,
             1,
             false,
             false);
   }
   
   /**
    * Tests "configurationExtractorInstanceCreationTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testMyInteger() throws Exception {
      doTest("/set/configurationExtractorMyInteger/test/MyInteger.java",
             "MyInteger",
             "/set/configurationExtractorMyInteger/oracle/",
             "StaticMember.xml",
             "testMyInteger_initial",
             ".xml",
             "testMyInteger_current",
             ".xml",
             null,
             1,
             2,
             false,
             false);
   }

   /**
    * Tests "configurationExtractorInstanceCreationTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testVariableArrayIndex() throws Exception {
      doTest("/set/configurationExtractorVariableArrayIndex/test/VariableArrayIndex.java",
             "VariableArrayIndex",
             "/set/configurationExtractorVariableArrayIndex/oracle/",
             "StaticMember.xml",
             "testVariableArrayIndex_initial",
             ".xml",
             "testVariableArrayIndex_current",
             ".xml",
             null,
             1,
             1,
             false,
             false);
   }
   
   /**
    * Tests "configurationExtractorInstanceCreationTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testStaticMember_OnReturnNode() throws Exception {
      doTest("/set/configurationExtractorStaticMember/test/StaticMember.java",
             "StaticMember",
             "/set/configurationExtractorStaticMember/oracle/",
             "StaticMember.xml",
             "testInstanceCreationTest_staticMember_initial",
             ".xml",
             "testInstanceCreationTest_staticMember_current",
             ".xml",
             null,
             1,
             2,
             false,
             false);
   }
   
   /**
    * Tests "configurationExtractorExistsQuantifierTest".
    * @throws Exception Occurred Exception.
    */
   public void testExistsQuantifierTest() throws Exception {
      doTest("/set/configurationExtractorExistsQuantifierTest/test/ExistsQuantifierTest.proof",
             "/set/configurationExtractorExistsQuantifierTest/oracle/",
             "ExistsQuantifierTest.xml",
             "testExistsQuantifierTest_initial",
             ".xml",
             "testExistsQuantifierTest_current",
             ".xml",
             null,
             1,
             2,
             false);
   }
   
   /**
    * Tests "configurationExtractorInstanceCreationTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testInstanceCreationTest_OnReturnNode() throws Exception {
      doTest("/set/configurationExtractorInstanceCreationTest/test/InstanceCreationTest.java",
             "InstanceCreationTest",
             "/set/configurationExtractorInstanceCreationTest/oracle/",
             "InstanceCreationTest.xml",
             "testInstanceCreationTest_onReturnNode_initial",
             ".xml",
             "testInstanceCreationTest_onReturnNode_current",
             ".xml",
             null,
             5,
             2,
             false,
             false);
   }

   /**
    * Tests "configurationExtractorWithOperationContractsTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testWithOperationContracts() throws Exception {
      doTest("/set/configurationExtractorWithOperationContractsTest/test/ConfigurationExtractorWithOperationContractsTest.java",
             "ConfigurationExtractorWithOperationContractsTest",
             "/set/configurationExtractorWithOperationContractsTest/oracle/",
             "ConfigurationExtractorWithOperationContractsTest.xml",
             "testWithOperationContracts_initial",
             ".xml",
             "testWithOperationContracts_current",
             ".xml",
             null,
             1,
             2,
             true);
   }
   
   /**
    * Tests "configurationExtractorAssociationSourceIsNotRepresentativeTermOfEquivalenceClass" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testAssociationSourceIsNotRepresentativeTermOfEquivalenceClass() throws Exception {
      doTest("/set/configurationExtractorAssociationSourceIsNotRepresentativeTermOfEquivalenceClass/test/AssociationSourceIsNotRepresentativeTermOfEquivalenceClass.java",
             "algorithm.AssociationSourceIsNotRepresentativeTermOfEquivalenceClass",
             "/set/configurationExtractorAssociationSourceIsNotRepresentativeTermOfEquivalenceClass/oracle/",
             "AssociationSourceIsNotRepresentativeTermOfEquivalenceClass.xml",
             "testAssociationSourceIsNotRepresentativeTermOfEquivalenceClass_initial",
             ".xml",
             "testAssociationSourceIsNotRepresentativeTermOfEquivalenceClass_current",
             ".xml",
             null,
             1,
             3,
             false);
   }
   
   /**
    * Tests "configurationExtractorArrayInstanceCreationTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testArrayInstanceCreationTest() throws Exception {
      doTest("/set/configurationExtractorArrayInstanceCreationTest/test/ArrayInstanceCreationTest.java",
             "ArrayInstanceCreationTest",
             "/set/configurationExtractorArrayInstanceCreationTest/oracle/",
             "ArrayInstanceCreationTest.xml",
             "testArrayInstanceCreationTest_initial",
             ".xml",
             "testArrayInstanceCreationTest_current",
             ".xml",
             null,
             1,
             2,
             false);
   }
   
   /**
    * Tests "configurationExtractorInstanceCreationTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testInstanceCreationTest() throws Exception {
      doTest("/set/configurationExtractorInstanceCreationTest/test/InstanceCreationTest.java",
             "InstanceCreationTest",
             "/set/configurationExtractorInstanceCreationTest/oracle/",
             "InstanceCreationTest.xml",
             "testInstanceCreationTest_initial",
             ".xml",
             "testInstanceCreationTest_current",
             ".xml",
             null,
             5,
             2,
             false);
   }
   
   /**
    * Tests "configurationExtractorSimpleArrayCreation" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleArrayCreation() throws Exception {
      doTest("/set/configurationExtractorSimpleArrayCreation/test/SimpleArrayCreation.java",
             "SimpleArrayCreation",
             "/set/configurationExtractorSimpleArrayCreation/oracle/",
             "SimpleArrayCreation.xml",
             "testSimpleArrayCreation_initial",
             ".xml",
             "testSimpleArrayCreation_current",
             ".xml",
             null,
             1,
             1,
             false);
   }
   
   /**
    * Tests "configurationExtractorMultiArrayIndexReadWriteAccess" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testMultiArrayIndexReadWriteAccess() throws Exception {
      doTest("/set/configurationExtractorMultiArrayIndexReadWriteAccess/test/MultiArrayIndexReadWriteAccess.java",
             "MultiArrayIndexReadWriteAccess",
             "/set/configurationExtractorMultiArrayIndexReadWriteAccess/oracle/",
             "MultiArrayIndexReadWriteAccess.xml",
             "testMultiArrayIndexReadWriteAccess_initial",
             ".xml",
             "testMultiArrayIndexReadWriteAccess_current",
             ".xml",
             null,
             1,
             1,
             false);
   }

   /**
    * Tests "configurationExtractorSimpleLinkedArrays" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedArrays() throws Exception {
      doTest("/set/configurationExtractorSimpleLinkedArrays/test/SimpleLinkedArrays.java",
             "SimpleLinkedArrays",
             "/set/configurationExtractorSimpleLinkedArrays/oracle/",
             "SimpleLinkedArrays.xml",
             "testSimpleLinkedArrays_initial",
             ".xml",
             "testSimpleLinkedArrays_current",
             ".xml",
             null,
             1,
             5,
             false);
   }
   
   /**
    * Tests "configurationExtractorObjectArrayIndexWriteAccess" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testObjectArrayIndexWriteAccess() throws Exception {
      doTest("/set/configurationExtractorObjectArrayIndexWriteAccess/test/ObjectArrayIndexWriteAccess.java",
             "ObjectArrayIndexWriteAccess",
             "/set/configurationExtractorObjectArrayIndexWriteAccess/oracle/",
             "ObjectArrayIndexWriteAccess.xml",
             "testObjectArrayIndexWriteAccess_initial",
             ".xml",
             "testObjectArrayIndexWriteAccess_current",
             ".xml",
             null,
             2,
             1,
             false);
   }
   
   /**
    * Tests "configurationExtractorArrayIndexWriteAccess" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testArrayIndexWriteAccess() throws Exception {
      doTest("/set/configurationExtractorArrayIndexWriteAccess/test/ArrayIndexWriteAccess.java",
             "ArrayIndexWriteAccess",
             "/set/configurationExtractorArrayIndexWriteAccess/oracle/",
             "ArrayIndexWriteAccess.xml",
             "testArrayIndexWriteAccess_initial",
             ".xml",
             "testArrayIndexWriteAccess_current",
             ".xml",
             null,
             1,
             1,
             false);
   }
   
   /**
    * Tests "configurationExtractorObjectArrayIndexReadAccess" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testObjectArrayIndexReadAccess() throws Exception {
      doTest("/set/configurationExtractorObjectArrayIndexReadAccess/test/ObjectArrayIndexReadAccess.java",
             "ObjectArrayIndexReadAccess",
             "/set/configurationExtractorObjectArrayIndexReadAccess/oracle/",
             "ObjectArrayIndexReadAccess.xml",
             "testObjectArrayIndexReadAccess_initial",
             ".xml",
             "testObjectArrayIndexReadAccess_current",
             ".xml",
             null,
             1,
             1,
             false);
   }
   
   /**
    * Tests "configurationExtractorOneAssignmentTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testArrayIndexReadAccess() throws Exception {
      doTest("/set/configurationExtractorArrayIndexReadAccess/test/ArrayIndexReadAccess.java",
             "ArrayIndexReadAccess",
             "/set/configurationExtractorArrayIndexReadAccess/oracle/",
             "ArrayIndexReadAccess.xml",
             "testArrayIndexReadAccess_initial",
             ".xml",
             "testArrayIndexReadAccess_current",
             ".xml",
             null,
             1,
             1,
             false);
   }
   
   /**
    * Tests "configurationExtractorOneAssignmentTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testOneAssignmentTest() throws Exception {
      doTest("/set/configurationExtractorOneAssignmentTest/test/OneAssignmentTest.java",
             "OneAssignmentTest",
             "/set/configurationExtractorOneAssignmentTest/oracle/",
             "OneAssignmentTest.xml",
             "testOneAssignmentTest_initial",
             ".xml",
             "testOneAssignmentTest_current",
             ".xml",
             null,
             1,
             5,
             false);
   }

   /**
    * Tests "configurationExtractorEmptyPathConditionAndNoUpdates" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testEmptyPathConditionAndNoUpdates() throws Exception {
      doTest("/set/configurationExtractorEmptyPathConditionAndNoUpdates/test/EmptyPathConditionAndNoUpdates.java",
             "EmptyPathConditionAndNoUpdates",
             "/set/configurationExtractorEmptyPathConditionAndNoUpdates/oracle/",
             "EmptyPathConditionAndNoUpdates.xml",
             "testEmptyPathConditionAndNoUpdates_initial",
             ".xml",
             "testEmptyPathConditionAndNoUpdates_current",
             ".xml",
             null,
             1,
             2,
             false);
   }
   
   /**
    * Tests "configurationExtractorSimpleLinkedOjbectsInsertion" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbectsInsertion() throws Exception {
      doTest("/set/configurationExtractorSimpleLinkedOjbectsInsertion/test/SimpleLinkedOjbectsInsertion.java",
             "SimpleLinkedOjbectsInsertion",
             "/set/configurationExtractorSimpleLinkedOjbectsInsertion/oracle/",
             "SimpleLinkedOjbectsInsertion.xml",
             "testSimpleLinkedOjbectsInsertion_initial",
             ".xml",
             "testSimpleLinkedOjbectsInsertion_current",
             ".xml",
             null,
             2,
             4,
             false);
   }
   
   /**
    * Tests "configurationExtractorIntegerConditionTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testObjectConditionTest() throws Exception {
      doTest("/set/configurationExtractorObjectConditionTest/test/ObjectConditionTest.java",
             "ObjectConditionTest",
             "/set/configurationExtractorObjectConditionTest/oracle/",
             "ObjectConditionTest.xml",
             "testObjectConditionTestt_initial",
             ".xml",
             "testObjectConditionTest_current",
             ".xml",
             null,
             1,
             1,
             false);
   }
   
   /**
    * Tests "configurationExtractorIntegerConditionTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testIntegerConditionTest() throws Exception {
      doTest("/set/configurationExtractorIntegerConditionTest/test/IntegerConditionTest.java",
             "IntegerConditionTest",
             "/set/configurationExtractorIntegerConditionTest/oracle/",
             "IsInstanceTest.xml",
             "testIntegerConditionTest_initial",
             ".xml",
             "testIntegerConditionTest_current",
             ".xml",
             null,
             1,
             1,
             false);
   }
   
   /**
    * Tests "configurationExtractorIsInstanceTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testIsInstanceTest() throws Exception {
      doTest("/set/configurationExtractorIsInstanceTest/test/IsInstanceTest.java",
             "IsInstanceTest",
             "/set/configurationExtractorIsInstanceTest/oracle/",
             "IsInstanceTest.xml",
             "testIsInstanceTest_initial",
             ".xml",
             "testIsInstanceTest_current",
             ".xml",
             null,
             1,
             2,
             false);
   }
   
   /**
    * Tests "configurationExtractorIsNullTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testIsNullTest() throws Exception {
      doTest("/set/configurationExtractorIsNullTest/test/IsNullTest.java",
             "IsNullTest",
             "/set/configurationExtractorIsNullTest/oracle/",
             "NullInEquivalenceClass.xml",
             "testIsNullTest_initial",
             ".xml",
             "testIsNullTest_current",
             ".xml",
             null,
             1,
             1,
             false);
   }
   
   /**
    * Tests "configurationExtractorSimpleLinkedOjbects" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbectsInstanceVariable() throws Exception {
      doTest("/set/configurationExtractorSimpleLinkedOjbectsInstanceVariable/test/SimpleLinkedOjbectsInstanceVariable.java",
             "SimpleLinkedOjbectsInstanceVariable",
             "/set/configurationExtractorSimpleLinkedOjbectsInstanceVariable/oracle/",
             "SimpleLinkedOjbectsInstanceVariable.xml",
             "testSimpleLinkedOjbectsInstanceVariable_initial",
             ".xml",
             "testSimpleLinkedOjbectsInstanceVariable_current",
             ".xml",
             null,
             1,
             4,
             false);
   }
   
   /**
    * Tests "configurationExtractorSimpleStaticAttributes" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleStaticAttributes() throws Exception {
      doTest("/set/configurationExtractorSimpleStaticAttributes/test/SimpleStaticAttributes.java",
             "SimpleStaticAttributes",
             "/set/configurationExtractorSimpleStaticAttributes/oracle/",
             "SimpleStaticAttributes.xml",
             "testSimpleStaticAttributes_initial",
             ".xml",
             "testSimpleStaticAttributes_current",
             ".xml",
             null,
             1,
             2,
             false);
   }
   
   /**
    * Tests "configurationExtractorSimpleArrayLength" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleArrayLength() throws Exception {
      doTest("/set/configurationExtractorSimpleArrayLength/test/SimpleArrayLength.java",
             "SimpleArrayLength",
             "/set/configurationExtractorSimpleArrayLength/oracle/",
             "SimpleArrayLength.xml",
             "testSimpleArrayLength_initial",
             ".xml",
             "testSimpleArrayLength_current",
             ".xml",
             null,
             1,
             1,
             false);
   }
   
   /**
    * Tests "configurationExtractorSimpleLinkedOjbectsDeletion" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbectsDeletion() throws Exception {
      doTest("/set/configurationExtractorSimpleLinkedOjbectsDeletion/test/SimpleLinkedOjbectsDeletion.java",
             "SimpleLinkedOjbectsDeletion",
             "/set/configurationExtractorSimpleLinkedOjbectsDeletion/oracle/",
             "SimpleLinkedOjbectsDeletion.xml",
             "testSimpleLinkedOjbectsDeletion_initial",
             ".xml",
             "testSimpleLinkedOjbectsDeletion_current",
             ".xml",
             null,
             1,
             4,
             false);
   }
   

   /**
    * Tests "configurationExtractorSimpleLinkedOjbectsDeletion" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbectsDeletionPreCondition() throws Exception {
      doTest("/set/configurationExtractorSimpleLinkedOjbectsDeletion/test/SimpleLinkedOjbectsDeletion.java",
             "SimpleLinkedOjbectsDeletion",
             "/set/configurationExtractorSimpleLinkedOjbectsDeletion/oracle/",
             "SimpleLinkedOjbectsDeletionPreCondition.xml",
             "testSimpleLinkedOjbectsDeletionPreCondition_initial",
             ".xml",
             "testSimpleLinkedOjbectsDeletionPreCondition_current",
             ".xml",
             "x != null & x.next != null & x.next.next != null",
             1,
             4,
             false);
   }
   
   /**
    * Tests "configurationExtractorSimpleLinkedOjbects" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbects() throws Exception {
      doTest("/set/configurationExtractorSimpleLinkedOjbects/test/SimpleLinkedOjbects.java",
             "SimpleLinkedOjbects",
             "/set/configurationExtractorSimpleLinkedOjbects/oracle/",
             "SimpleLinkedOjbects.xml",
             "testSimpleLinkedOjbects_initial",
             ".xml",
             "testSimpleLinkedOjbects_current",
             ".xml",
             null,
             1,
             4,
             false);
   }
   
   /**
    * Tests "configurationExtractorSimpleLinkedOjbects" with precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbectsPreCondition() throws Exception {
      doTest("/set/configurationExtractorSimpleLinkedOjbects/test/SimpleLinkedOjbects.java",
             "SimpleLinkedOjbects",
             "/set/configurationExtractorSimpleLinkedOjbects/oracle/",
             "SimpleLinkedOjbectsPreCondition.xml",
             "testSimpleLinkedOjbectsPreCondition_initial",
             ".xml",
             "testSimpleLinkedOjbectsPreCondition_current",
             ".xml",
             "x != null & x.next != null & x.next.next != null",
             1,
             4,
             false);
   }
   
   /**
    * Executes the test steps.
    * @param javaPathInkeyRepDirectory The path to the Java file.
    * @param containerTypeName The class name.
    * @param oraclePathInBaseDir The path to the oracle directory.
    * @param symbolicExecutionOracleFileName File name of the symbolic execution oracle file.
    * @param initialStatesOraclePrefix Prefix for initial memory layout oracles.
    * @param initialStatesOracleFileExtension Initial memory layout oracle file extension.
    * @param currentStatesOraclePrefix Prefix for current memory layout oracles.
    * @param currentStatesOracleFileExtension Current memory layout oracle file extension.
    * @param precondition An optional precondition.
    * @param useOperationContracts Use operation contracts?
    * @throws Exception Occurred Exception.
    */
   protected void doTest(String javaPathInkeyRepDirectory,
                         String containerTypeName,
                         String oraclePathInBaseDir,
                         String symbolicExecutionOracleFileName,
                         String initialStatesOraclePrefix,
                         String initialStatesOracleFileExtension,
                         String currentStatesOraclePrefix,
                         String currentStatesOracleFileExtension,
                         String precondition,
                         int numberOfReturnNodeInMostLeftBranch,
                         int expectedNumberOfLayouts,
                         boolean useOperationContracts) throws Exception {
      doTest(javaPathInkeyRepDirectory,
             containerTypeName,
             oraclePathInBaseDir,
             symbolicExecutionOracleFileName,
             initialStatesOraclePrefix,
             initialStatesOracleFileExtension,
             currentStatesOraclePrefix,
             currentStatesOracleFileExtension,
             precondition,
             numberOfReturnNodeInMostLeftBranch,
             expectedNumberOfLayouts,
             useOperationContracts,
             true);
   }

   /**
    * Executes the test steps.
    * @param javaPathInkeyRepDirectory The path to the Java file.
    * @param containerTypeName The class name.
    * @param oraclePathInBaseDir The path to the oracle directory.
    * @param symbolicExecutionOracleFileName File name of the symbolic execution oracle file.
    * @param initialStatesOraclePrefix Prefix for initial memory layout oracles.
    * @param initialStatesOracleFileExtension Initial memory layout oracle file extension.
    * @param currentStatesOraclePrefix Prefix for current memory layout oracles.
    * @param currentStatesOracleFileExtension Current memory layout oracle file extension.
    * @param precondition An optional precondition.
    * @param useOperationContracts Use operation contracts?
    * @throws Exception Occurred Exception.
    */
   protected void doTest(String javaPathInkeyRepDirectory,
                         String containerTypeName,
                         String oraclePathInBaseDir,
                         String symbolicExecutionOracleFileName,
                         String initialStatesOraclePrefix,
                         String initialStatesOracleFileExtension,
                         String currentStatesOraclePrefix,
                         String currentStatesOracleFileExtension,
                         String precondition,
                         int numberOfReturnNodeInMostLeftBranch,
                         int expectedNumberOfLayouts,
                         boolean useOperationContracts,
                         boolean onReturnStatementNode) throws Exception {
      HashMap<String, String> originalTacletOptions = null;
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try {
         // Define test settings
         final String methodFullName = "compute";
         // Make sure that the correct taclet options are defined.
         originalTacletOptions = setDefaultTacletOptions(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName);
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, precondition, false, useOperationContracts, false, false, false, false, false, false, false, true);
         setOneStepSimplificationEnabled(null, true);
         // Resume
         resume(env.getUi(), env.getBuilder(), oraclePathInBaseDir + symbolicExecutionOracleFileName, testCaseDirectory);
         // Perform test steps
         doTestSteps(env, oraclePathInBaseDir, symbolicExecutionOracleFileName, initialStatesOraclePrefix, initialStatesOracleFileExtension, currentStatesOraclePrefix, currentStatesOracleFileExtension, precondition, numberOfReturnNodeInMostLeftBranch, expectedNumberOfLayouts, onReturnStatementNode);
      }
      finally {
         // Restore original options
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         restoreTacletOptions(originalTacletOptions);
         if (env != null) {
            env.dispose();
         }
      }
   }

   /**
    * Executes the test steps.
    * @param proofFilePathInkeyRepDirectory The path to the Proof file.
    * @param containerTypeName The class name.
    * @param oraclePathInBaseDir The path to the oracle directory.
    * @param symbolicExecutionOracleFileName File name of the symbolic execution oracle file.
    * @param initialStatesOraclePrefix Prefix for initial memory layout oracles.
    * @param initialStatesOracleFileExtension Initial memory layout oracle file extension.
    * @param currentStatesOraclePrefix Prefix for current memory layout oracles.
    * @param currentStatesOracleFileExtension Current memory layout oracle file extension.
    * @param precondition An optional precondition.
    * @param useOperationContracts Use operation contracts?
    * @throws Exception Occurred Exception.
    */
   protected void doTest(String proofFilePathInkeyRepDirectory,
                         String oraclePathInBaseDir,
                         String symbolicExecutionOracleFileName,
                         String initialStatesOraclePrefix,
                         String initialStatesOracleFileExtension,
                         String currentStatesOraclePrefix,
                         String currentStatesOracleFileExtension,
                         String precondition,
                         int numberOfReturnNodeInMostLeftBranch,
                         int expectedNumberOfLayouts,
                         boolean onReturnStatementNode) throws Exception {
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
      try {
         // Load proof file
         env = createSymbolicExecutionEnvironment(testCaseDirectory, proofFilePathInkeyRepDirectory, false, false, false, false, false, false, false, false, false, false, true);
         // Perform test steps
         doTestSteps(env, oraclePathInBaseDir, symbolicExecutionOracleFileName, initialStatesOraclePrefix, initialStatesOracleFileExtension, currentStatesOraclePrefix, currentStatesOracleFileExtension, precondition, numberOfReturnNodeInMostLeftBranch, expectedNumberOfLayouts, onReturnStatementNode);
      }
      finally {
         if (env != null) {
            env.dispose();
         }
      }
   }
   
   protected void doTestSteps(SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env,
                              String oraclePathInBaseDir,
                              String symbolicExecutionOracleFileName,
                              String initialStatesOraclePrefix,
                              String initialStatesOracleFileExtension,
                              String currentStatesOraclePrefix,
                              String currentStatesOracleFileExtension,
                              String precondition,
                              int numberOfReturnNodeInMostLeftBranch,
                              int expectedNumberOfLayouts,
                              boolean onReturnStatementNode) throws Exception {
      // Find most left method return node
      IExecutionNode<?> returnNode = env.getBuilder().getStartNode();
      int foundReturnStatement = 0;
      while (foundReturnStatement < numberOfReturnNodeInMostLeftBranch && returnNode.getChildren().length >= 1) {
         returnNode = returnNode.getChildren()[0];
         if (returnNode instanceof IExecutionMethodReturn) {
            foundReturnStatement++;
         }
      }
      assertTrue(returnNode instanceof IExecutionMethodReturn);
      IExecutionNode<?> nodeToTest;
      if (onReturnStatementNode) {
         // Get the return statement which is returned in returnNode
         IExecutionNode<?> returnStatement = returnNode.getParent();
         while (!(returnStatement instanceof IExecutionStatement)) {
            if (returnStatement instanceof IExecutionStatement) {
               foundReturnStatement++;
            }
            returnStatement = returnStatement.getParent();
         }
         assertNotNull(returnStatement);
         assertTrue(returnStatement.getName().startsWith("return"));
         nodeToTest = returnStatement;
      }
      else {
         nodeToTest = returnNode;
      }
      // Extract possible heaps
      SymbolicLayoutExtractor extractor = new SymbolicLayoutExtractor(nodeToTest.getProofNode(), nodeToTest.getModalityPIO(), false, false, true);
      extractor.analyse();
      // Test the initial memory layouts (first time with lazy computation)
      List<ISymbolicLayout> initialLayoutsFirstTime = new ArrayList<ISymbolicLayout>(extractor.getLayoutsCount());
      assertEquals(expectedNumberOfLayouts, extractor.getLayoutsCount());
      for (int i = 0; i < extractor.getLayoutsCount(); i++) {
         ISymbolicLayout current = extractor.getInitialLayout(i);
         initialLayoutsFirstTime.add(current);
         String oracleFile = oraclePathInBaseDir + initialStatesOraclePrefix + i + initialStatesOracleFileExtension;
         createOracleFile(current, oracleFile);
         if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            SymbolicLayoutReader reader = new SymbolicLayoutReader();
            ISymbolicLayout expected = reader.read(new File(testCaseDirectory, oracleFile));
            assertNotNull(expected);
            assertModel(expected, current);
         }
      }
      // Test the initial memory layouts (second time with same memory layouts)
      for (int i = 0; i < extractor.getLayoutsCount(); i++) {
         ISymbolicLayout current = extractor.getInitialLayout(i);
         assertSame(initialLayoutsFirstTime.get(i), current);
      }
      // Test the current memory layouts (first time with lazy computation)
      List<ISymbolicLayout> currentLayoutsFirstTime = new ArrayList<ISymbolicLayout>(extractor.getLayoutsCount());
      for (int i = 0; i < extractor.getLayoutsCount(); i++) {
         ISymbolicLayout current = extractor.getCurrentLayout(i);
         currentLayoutsFirstTime.add(current);
         String oracleFile = oraclePathInBaseDir + currentStatesOraclePrefix + i + currentStatesOracleFileExtension;
         createOracleFile(current, oracleFile);
         if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            SymbolicLayoutReader reader = new SymbolicLayoutReader();
            ISymbolicLayout expected = reader.read(new File(testCaseDirectory, oracleFile));
            assertNotNull(expected);
            assertModel(expected, current);
         }
      }
      // Test the current memory layouts (second time with same memory layouts)
      for (int i = 0; i < extractor.getLayoutsCount(); i++) {
         ISymbolicLayout current = extractor.getCurrentLayout(i);
         assertSame(currentLayoutsFirstTime.get(i), current);
      }
   }
   
   /**
    * Compares the given {@link ISymbolicLayout}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   protected static void createOracleFile(ISymbolicLayout model, 
                                          String oraclePathInBaseDirFile) throws IOException, ProofInputException {
      if (tempNewOracleDirectory != null && tempNewOracleDirectory.isDirectory()) {
         // Create sub folder structure
         File oracleFile = new File(tempNewOracleDirectory, oraclePathInBaseDirFile);
         oracleFile.getParentFile().mkdirs();
         // Create oracle file
         SymbolicLayoutWriter writer = new SymbolicLayoutWriter();
         writer.write(model, SymbolicLayoutWriter.DEFAULT_ENCODING, oracleFile);
         // Print message to the user.
         printOracleDirectory();
      }
   }
   
   public static void assertModel(ISymbolicLayout expected, ISymbolicLayout current) {
      if (expected != null) {
         assertNotNull(current);
         assertState(expected.getState(), current.getState());
         assertObjects(expected.getObjects(), current.getObjects());
         assertEquivalenceClasses(expected.getEquivalenceClasses(), current.getEquivalenceClasses());
      }
      else {
         assertNull(current);
      }
   }
   
   /**
    * Compares the given {@link ISymbolicState}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   public static void assertState(ISymbolicState expected, ISymbolicState current) {
      if (expected != null) {
         assertNotNull(current);
         assertEquals(expected.getName(), current.getName());
         assertValues(expected.getValues(), current.getValues());
         assertAssociations(expected.getAssociations(), current.getAssociations());
      }
      else {
         assertNull(current);
      }
   }
   
   /**
    * Compares the given {@link ISymbolicObject}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   public static void assertObjects(ImmutableList<ISymbolicObject> expected, ImmutableList<ISymbolicObject> current) {
      assertNotNull(expected);
      assertNotNull(current);
      assertEquals(expected.size(), current.size());
      Iterator<ISymbolicObject> expectedIter = expected.iterator();
      Iterator<ISymbolicObject> currentIter = current.iterator();
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         assertObject(expectedIter.next(), currentIter.next(), true);
      }
      assertFalse(expectedIter.hasNext());
      assertFalse(currentIter.hasNext());
   }
   
   /**
    * Compares the given {@link ISymbolicObject}s.
    * @param expected The expected instance.
    * @param current The current instance.
    * @param compareAssociations Compare contained associations?
    */
   public static void assertObject(ISymbolicObject expected, ISymbolicObject current, boolean compareAssociations) {
      if (expected != null) {
         assertNotNull(current);
         assertEquals(expected.getNameString(), current.getNameString());
         assertEquals(expected.getTypeString(), current.getTypeString());
         assertValues(expected.getValues(), current.getValues());
         if (compareAssociations) {
            assertAssociations(expected.getAssociations(), current.getAssociations());
         }
      }
      else {
         assertNull(current);
      }
   }
   
   /**
    * Compares the given {@link ISymbolicEquivalenceClass}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   public static void assertEquivalenceClasses(ImmutableList<ISymbolicEquivalenceClass> expected, ImmutableList<ISymbolicEquivalenceClass> current) {
      assertNotNull(expected);
      assertNotNull(current);
      assertEquals(expected.size(), current.size());
      Iterator<ISymbolicEquivalenceClass> expectedIter = expected.iterator();
      Iterator<ISymbolicEquivalenceClass> currentIter = current.iterator();
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         assertEquivalenceClass(expectedIter.next(), currentIter.next());
      }
      assertFalse(expectedIter.hasNext());
      assertFalse(currentIter.hasNext());
   }
   
   /**
    * Compares the given {@link ISymbolicEquivalenceClass}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   public static void assertEquivalenceClass(ISymbolicEquivalenceClass expected, ISymbolicEquivalenceClass current) {
      if (expected != null) {
         assertNotNull(current);
         assertStringListEqualsIgnoreWhiteSpace(expected.getTermStrings(), current.getTermStrings());
         assertEquals(expected.getRepresentativeString(), current.getRepresentativeString());
      }
      else {
         assertNull(current);
      }
   }
   
   /**
    * Compares the given {@link ImmutableList}s ignoring white space.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   public static void assertStringListEqualsIgnoreWhiteSpace(ImmutableList<String> expected, ImmutableList<String> current) {
      assertNotNull(expected);
      assertNotNull(current);
      assertEquals(expected.size(), current.size());
      Iterator<String> expectedIter = expected.iterator();
      Iterator<String> currentIter = current.iterator();
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         String nextExpected = expectedIter.next();
         String nextCurrent = currentIter.next();
         assertTrue("\"" + nextExpected + "\" does not match \"" + nextCurrent + "\"", StringUtil.equalIgnoreWhiteSpace(nextExpected, nextCurrent));
      }
      assertFalse(expectedIter.hasNext());
      assertFalse(currentIter.hasNext());
   }
   
   /**
    * Compares the given {@link ISymbolicValue}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   public static void assertValues(ImmutableList<ISymbolicValue> expected, ImmutableList<ISymbolicValue> current) {
      assertNotNull(expected);
      assertNotNull(current);
      assertEquals(expected.size(), current.size());
      Iterator<ISymbolicValue> expectedIter = expected.iterator();
      Iterator<ISymbolicValue> currentIter = current.iterator();
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         assertValue(expectedIter.next(), currentIter.next());
      }
      assertFalse(expectedIter.hasNext());
      assertFalse(currentIter.hasNext());
   }

   /**
    * Compares the given {@link ISymbolicValue}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   public static void assertValue(ISymbolicValue expected, ISymbolicValue current) {
      if (expected != null) {
         assertNotNull(current);
         assertEquals(expected.getName(), current.getName());
         assertEquals(expected.getProgramVariableString(), current.getProgramVariableString());
         assertEquals(expected.isArrayIndex(), current.isArrayIndex());
         assertEquals(expected.getArrayIndexString(), current.getArrayIndexString());
         assertTrue("\"" + expected.getValueString() + "\" does not match \"" + current.getValueString() + "\"", StringUtil.equalIgnoreWhiteSpace(expected.getValueString(), current.getValueString()));
         assertEquals(expected.getTypeString(), current.getTypeString());
         assertEquals(expected.getConditionString(), current.getConditionString());
      }
      else {
         assertNull(current);
      }
   }
   
   /**
    * Compares the given {@link ISymbolicAssociation}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   public static void assertAssociations(ImmutableList<ISymbolicAssociation> expected, ImmutableList<ISymbolicAssociation> current) {
      assertNotNull(expected);
      assertNotNull(current);
      assertEquals(expected.size(), current.size());
      Iterator<ISymbolicAssociation> expectedIter = expected.iterator();
      Iterator<ISymbolicAssociation> currentIter = current.iterator();
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         assertAssociation(expectedIter.next(), currentIter.next());
      }
      assertFalse(expectedIter.hasNext());
      assertFalse(currentIter.hasNext());
   }
   
   /**
    * Compares the given {@link ISymbolicAssociation}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   public static void assertAssociation(ISymbolicAssociation expected, ISymbolicAssociation current) {
      if (expected != null) {
         assertNotNull(current);
         assertEquals(expected.getName(), current.getName());
         assertEquals(expected.getProgramVariableString(), current.getProgramVariableString());
         assertEquals(expected.isArrayIndex(), current.isArrayIndex());
         assertEquals(expected.getArrayIndexString(), current.getArrayIndexString());
         assertObject(expected.getTarget(), current.getTarget(), false);
         assertEquals(expected.getConditionString(), current.getConditionString());
      }
      else {
         assertNull(current);
      }
   }
}