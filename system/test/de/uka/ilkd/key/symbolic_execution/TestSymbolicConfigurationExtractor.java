package de.uka.ilkd.key.symbolic_execution;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicConfiguration;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicState;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Tests {@link SymbolicConfigurationExtractor}.
 * @author Martin Hentschel
 */
public class TestSymbolicConfigurationExtractor extends AbstractSymbolicExecutionTestCase {
//   public void testSimpleLinkedOjbectsWithAdditionalInstances() throws Exception {
//      doTest("examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsWithAdditionalInstances/test/SimpleLinkedOjbectsWithAdditionalInstances.java",
//             "SimpleLinkedOjbectsWithAdditionalInstances",
//             "examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsWithAdditionalInstances/oracle/",
//             "SimpleLinkedOjbectsWithAdditionalInstances.xml",
//             "testSimpleLinkedOjbectsWithAdditionalInstances_initial",
//             ".xml",
//             "testSimpleLinkedOjbectsWithAdditionalInstances_current",
//             ".xml",
//             null);
//   }
   
//   public void testSimpleLinkedOjbectsWithAdditionalInstancesPreCondition() throws Exception {
//      doTest("examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsWithAdditionalInstances/test/SimpleLinkedOjbectsWithAdditionalInstances.java",
//             "SimpleLinkedOjbectsWithAdditionalInstances",
//             "examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsWithAdditionalInstances/oracle/",
//             "SimpleLinkedOjbectsWithAdditionalInstances.xml",
//             "testSimpleLinkedOjbectsWithAdditionalInstancesPreCondition_initial",
//             ".xml",
//             "testSimpleLinkedOjbectsWithAdditionalInstancesPreCondition_current",
//             ".xml",
//             "x != null & x.next != null & x.next.next != null & a != null & a.x == 42 & b != null");
//   }
   
   /**
    * Tests "configurationExtractorArrayInstanceCreationTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testArrayInstanceCreationTest() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorArrayInstanceCreationTest/test/ArrayInstanceCreationTest.java",
             "ArrayInstanceCreationTest",
             "examples/_testcase/set/configurationExtractorArrayInstanceCreationTest/oracle/",
             "ArrayInstanceCreationTest.xml",
             "testArrayInstanceCreationTest_initial",
             ".xml",
             "testArrayInstanceCreationTest_current",
             ".xml",
             null,
             1,
             2);
   }
   
   /**
    * Tests "configurationExtractorInstanceCreationTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testInstanceCreationTest() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorInstanceCreationTest/test/InstanceCreationTest.java",
             "InstanceCreationTest",
             "examples/_testcase/set/configurationExtractorInstanceCreationTest/oracle/",
             "InstanceCreationTest.xml",
             "testInstanceCreationTest_initial",
             ".xml",
             "testInstanceCreationTest_current",
             ".xml",
             null,
             5,
             2);
   }
   
   /**
    * Tests "configurationExtractorSimpleArrayCreation" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleArrayCreation() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorSimpleArrayCreation/test/SimpleArrayCreation.java",
             "SimpleArrayCreation",
             "examples/_testcase/set/configurationExtractorSimpleArrayCreation/oracle/",
             "SimpleArrayCreation.xml",
             "testSimpleArrayCreation_initial",
             ".xml",
             "testSimpleArrayCreation_current",
             ".xml",
             null,
             1,
             1);
   }
   
   /**
    * Tests "configurationExtractorMultiArrayIndexReadWriteAccess" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testMultiArrayIndexReadWriteAccess() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorMultiArrayIndexReadWriteAccess/test/MultiArrayIndexReadWriteAccess.java",
             "MultiArrayIndexReadWriteAccess",
             "examples/_testcase/set/configurationExtractorMultiArrayIndexReadWriteAccess/oracle/",
             "MultiArrayIndexReadWriteAccess.xml",
             "testMultiArrayIndexReadWriteAccess_initial",
             ".xml",
             "testMultiArrayIndexReadWriteAccess_current",
             ".xml",
             null,
             1,
             1);
   }

   /**
    * Tests "configurationExtractorSimpleLinkedArrays" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedArrays() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorSimpleLinkedArrays/test/SimpleLinkedArrays.java",
             "SimpleLinkedArrays",
             "examples/_testcase/set/configurationExtractorSimpleLinkedArrays/oracle/",
             "SimpleLinkedArrays.xml",
             "testSimpleLinkedArrays_initial",
             ".xml",
             "testSimpleLinkedArrays_current",
             ".xml",
             null,
             1,
             5);
   }
   
   /**
    * Tests "configurationExtractorObjectArrayIndexWriteAccess" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testObjectArrayIndexWriteAccess() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorObjectArrayIndexWriteAccess/test/ObjectArrayIndexWriteAccess.java",
             "ObjectArrayIndexWriteAccess",
             "examples/_testcase/set/configurationExtractorObjectArrayIndexWriteAccess/oracle/",
             "ObjectArrayIndexWriteAccess.xml",
             "testObjectArrayIndexWriteAccess_initial",
             ".xml",
             "testObjectArrayIndexWriteAccess_current",
             ".xml",
             null,
             2,
             1);
   }
   
   /**
    * Tests "configurationExtractorArrayIndexWriteAccess" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testArrayIndexWriteAccess() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorArrayIndexWriteAccess/test/ArrayIndexWriteAccess.java",
             "ArrayIndexWriteAccess",
             "examples/_testcase/set/configurationExtractorArrayIndexWriteAccess/oracle/",
             "ArrayIndexWriteAccess.xml",
             "testArrayIndexWriteAccess_initial",
             ".xml",
             "testArrayIndexWriteAccess_current",
             ".xml",
             null,
             1,
             1);
   }
   
   /**
    * Tests "configurationExtractorObjectArrayIndexReadAccess" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testObjectArrayIndexReadAccess() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorObjectArrayIndexReadAccess/test/ObjectArrayIndexReadAccess.java",
             "ObjectArrayIndexReadAccess",
             "examples/_testcase/set/configurationExtractorObjectArrayIndexReadAccess/oracle/",
             "ObjectArrayIndexReadAccess.xml",
             "testObjectArrayIndexReadAccess_initial",
             ".xml",
             "testObjectArrayIndexReadAccess_current",
             ".xml",
             null,
             1,
             1);
   }
   
   /**
    * Tests "configurationExtractorOneAssignmentTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testArrayIndexReadAccess() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorArrayIndexReadAccess/test/ArrayIndexReadAccess.java",
             "ArrayIndexReadAccess",
             "examples/_testcase/set/configurationExtractorArrayIndexReadAccess/oracle/",
             "ArrayIndexReadAccess.xml",
             "testArrayIndexReadAccess_initial",
             ".xml",
             "testArrayIndexReadAccess_current",
             ".xml",
             null,
             1,
             1);
   }
   
   /**
    * Tests "configurationExtractorOneAssignmentTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testOneAssignmentTest() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorOneAssignmentTest/test/OneAssignmentTest.java",
             "OneAssignmentTest",
             "examples/_testcase/set/configurationExtractorOneAssignmentTest/oracle/",
             "OneAssignmentTest.xml",
             "testOneAssignmentTest_initial",
             ".xml",
             "testOneAssignmentTest_current",
             ".xml",
             null,
             1,
             5);
   }

   /**
    * Tests "configurationExtractorEmptyPathConditionAndNoUpdates" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testEmptyPathConditionAndNoUpdates() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorEmptyPathConditionAndNoUpdates/test/EmptyPathConditionAndNoUpdates.java",
             "EmptyPathConditionAndNoUpdates",
             "examples/_testcase/set/configurationExtractorEmptyPathConditionAndNoUpdates/oracle/",
             "EmptyPathConditionAndNoUpdates.xml",
             "testEmptyPathConditionAndNoUpdates_initial",
             ".xml",
             "testEmptyPathConditionAndNoUpdates_current",
             ".xml",
             null,
             1,
             2);
   }
   
   /**
    * Tests "configurationExtractorSimpleLinkedOjbectsInsertion" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbectsInsertion() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsInsertion/test/SimpleLinkedOjbectsInsertion.java",
             "SimpleLinkedOjbectsInsertion",
             "examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsInsertion/oracle/",
             "SimpleLinkedOjbectsInsertion.xml",
             "testSimpleLinkedOjbectsInsertion_initial",
             ".xml",
             "testSimpleLinkedOjbectsInsertion_current",
             ".xml",
             null,
             2,
             4);
   }
   
   /**
    * Tests "configurationExtractorIntegerConditionTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testObjectConditionTest() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorObjectConditionTest/test/ObjectConditionTest.java",
             "ObjectConditionTest",
             "examples/_testcase/set/configurationExtractorObjectConditionTest/oracle/",
             "ObjectConditionTest.xml",
             "testObjectConditionTestt_initial",
             ".xml",
             "testObjectConditionTest_current",
             ".xml",
             null,
             1,
             1);
   }
   
   /**
    * Tests "configurationExtractorIntegerConditionTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testIntegerConditionTest() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorIntegerConditionTest/test/IntegerConditionTest.java",
             "IntegerConditionTest",
             "examples/_testcase/set/configurationExtractorIntegerConditionTest/oracle/",
             "IsInstanceTest.xml",
             "testIntegerConditionTest_initial",
             ".xml",
             "testIntegerConditionTest_current",
             ".xml",
             null,
             1,
             1);
   }
   
   /**
    * Tests "configurationExtractorIsInstanceTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testIsInstanceTest() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorIsInstanceTest/test/IsInstanceTest.java",
             "IsInstanceTest",
             "examples/_testcase/set/configurationExtractorIsInstanceTest/oracle/",
             "IsInstanceTest.xml",
             "testIsInstanceTest_initial",
             ".xml",
             "testIsInstanceTest_current",
             ".xml",
             null,
             1,
             2);
   }
   
   /**
    * Tests "configurationExtractorIsNullTest" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testIsNullTest() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorIsNullTest/test/IsNullTest.java",
             "IsNullTest",
             "examples/_testcase/set/configurationExtractorIsNullTest/oracle/",
             "NullInEquivalenceClass.xml",
             "testIsNullTest_initial",
             ".xml",
             "testIsNullTest_current",
             ".xml",
             null,
             1,
             1);
   }
   
   /**
    * Tests "configurationExtractorSimpleLinkedOjbects" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbectsInstanceVariable() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsInstanceVariable/test/SimpleLinkedOjbectsInstanceVariable.java",
             "SimpleLinkedOjbectsInstanceVariable",
             "examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsInstanceVariable/oracle/",
             "SimpleLinkedOjbectsInstanceVariable.xml",
             "testSimpleLinkedOjbectsInstanceVariable_initial",
             ".xml",
             "testSimpleLinkedOjbectsInstanceVariable_current",
             ".xml",
             null,
             1,
             4);
   }
   
   /**
    * Tests "configurationExtractorSimpleStaticAttributes" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleStaticAttributes() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorSimpleStaticAttributes/test/SimpleStaticAttributes.java",
             "SimpleStaticAttributes",
             "examples/_testcase/set/configurationExtractorSimpleStaticAttributes/oracle/",
             "SimpleStaticAttributes.xml",
             "testSimpleStaticAttributes_initial",
             ".xml",
             "testSimpleStaticAttributes_current",
             ".xml",
             null,
             1,
             2);
   }
   
   /**
    * Tests "configurationExtractorSimpleArrayLength" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleArrayLength() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorSimpleArrayLength/test/SimpleArrayLength.java",
             "SimpleArrayLength",
             "examples/_testcase/set/configurationExtractorSimpleArrayLength/oracle/",
             "SimpleArrayLength.xml",
             "testSimpleArrayLength_initial",
             ".xml",
             "testSimpleArrayLength_current",
             ".xml",
             null,
             1,
             1);
   }
   
   /**
    * Tests "configurationExtractorSimpleLinkedOjbectsDeletion" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbectsDeletion() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsDeletion/test/SimpleLinkedOjbectsDeletion.java",
             "SimpleLinkedOjbectsDeletion",
             "examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsDeletion/oracle/",
             "SimpleLinkedOjbectsDeletion.xml",
             "testSimpleLinkedOjbectsDeletion_initial",
             ".xml",
             "testSimpleLinkedOjbectsDeletion_current",
             ".xml",
             null,
             1,
             4);
   }
   

   /**
    * Tests "configurationExtractorSimpleLinkedOjbectsDeletion" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbectsDeletionPreCondition() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsDeletion/test/SimpleLinkedOjbectsDeletion.java",
             "SimpleLinkedOjbectsDeletion",
             "examples/_testcase/set/configurationExtractorSimpleLinkedOjbectsDeletion/oracle/",
             "SimpleLinkedOjbectsDeletionPreCondition.xml",
             "testSimpleLinkedOjbectsDeletionPreCondition_initial",
             ".xml",
             "testSimpleLinkedOjbectsDeletionPreCondition_current",
             ".xml",
             "x != null & x.next != null & x.next.next != null",
             1,
             4);
   }
   
   /**
    * Tests "configurationExtractorSimpleLinkedOjbects" without precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbects() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorSimpleLinkedOjbects/test/SimpleLinkedOjbects.java",
             "SimpleLinkedOjbects",
             "examples/_testcase/set/configurationExtractorSimpleLinkedOjbects/oracle/",
             "SimpleLinkedOjbects.xml",
             "testSimpleLinkedOjbects_initial",
             ".xml",
             "testSimpleLinkedOjbects_current",
             ".xml",
             null,
             1,
             4);
   }
   
   /**
    * Tests "configurationExtractorSimpleLinkedOjbects" with precondition.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLinkedOjbectsPreCondition() throws Exception {
      doTest("examples/_testcase/set/configurationExtractorSimpleLinkedOjbects/test/SimpleLinkedOjbects.java",
             "SimpleLinkedOjbects",
             "examples/_testcase/set/configurationExtractorSimpleLinkedOjbects/oracle/",
             "SimpleLinkedOjbectsPreCondition.xml",
             "testSimpleLinkedOjbectsPreCondition_initial",
             ".xml",
             "testSimpleLinkedOjbectsPreCondition_current",
             ".xml",
             "x != null & x.next != null & x.next.next != null",
             1,
             4);
   }
   
   /**
    * Executes the test steps.
    * @param javaPathInkeyRepDirectory The path to the Java file.
    * @param containerTypeName The class name.
    * @param oraclePathInBaseDir The path to the oracle directory.
    * @param symbolicExecutionOracleFileName File name of the symbolic execution oracle file.
    * @param initialStatesOraclePrefix Prefix for initial configuration oracles.
    * @param initialStatesOracleFileExtension Initial configuration oracle file extension.
    * @param currentStatesOraclePrefix Prefix for current configuration oracles.
    * @param currentStatesOracleFileExtension Current configuration oracle file extension.
    * @param precondition An optional precondition.
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
                         int expectedNumberOfConfigurations) throws Exception {
      String originalRuntimeExceptions = null;
      try {
         // Define test settings
         final String methodFullName = "compute";
         // Store original settings of KeY which requires that at least one proof was instantiated.
         if (!SymbolicExecutionUtil.isChoiceSettingInitialised()) {
            createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, precondition, false, false, false);
         }
         originalRuntimeExceptions = SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);
         assertNotNull(originalRuntimeExceptions);
         SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW);
         // Create proof environment for symbolic execution
         SymbolicExecutionEnvironment<CustomConsoleUserInterface> env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, precondition, false, false, false);
         // Resume
         resume(env.getUi(), env.getBuilder(), oraclePathInBaseDir + symbolicExecutionOracleFileName, keyRepDirectory);
         // Find most left method return node
         IExecutionNode returnNode = env.getBuilder().getStartNode();
         int foundReturnStatement = 0;
         while (foundReturnStatement < numberOfReturnNodeInMostLeftBranch && returnNode.getChildren().length >= 1) {
            returnNode = returnNode.getChildren()[0];
            if (returnNode instanceof IExecutionMethodReturn) {
               foundReturnStatement++;
            }
         }
         assertTrue(returnNode instanceof IExecutionMethodReturn);
         // Get the return statement which is returned in returnNode
         IExecutionNode returnStatement = returnNode.getParent();
         while (!(returnStatement instanceof IExecutionStatement)) {
            if (returnStatement instanceof IExecutionStatement) {
               foundReturnStatement++;
            }
            returnStatement = returnStatement.getParent();
         }
         assertNotNull(returnStatement);
         assertTrue(returnStatement.getName().startsWith("return"));
         // Extract possible heaps
         SymbolicConfigurationExtractor extractor = new SymbolicConfigurationExtractor(returnStatement.getProofNode());
         extractor.analyse();
         // Test the initial configurations (first time with lazy computation)
         List<ISymbolicConfiguration> initialConfigurationsFirstTime = new ArrayList<ISymbolicConfiguration>(extractor.getConfigurationsCount());
         assertEquals(expectedNumberOfConfigurations, extractor.getConfigurationsCount());
         for (int i = 0; i < extractor.getConfigurationsCount(); i++) {
            ISymbolicConfiguration current = extractor.getInitialConfiguration(i);
            initialConfigurationsFirstTime.add(current);
            String oracleFile = oraclePathInBaseDir + initialStatesOraclePrefix + i + initialStatesOracleFileExtension;
            createOracleFile(current, oracleFile);
            if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
               SymbolicConfigurationReader reader = new SymbolicConfigurationReader();
               ISymbolicConfiguration expected = reader.read(new File(keyRepDirectory, oracleFile));
               assertNotNull(expected);
               assertModel(expected, current);
            }
         }
         // Test the initial configurations (second time with same configurations)
         for (int i = 0; i < extractor.getConfigurationsCount(); i++) {
            ISymbolicConfiguration current = extractor.getInitialConfiguration(i);
            assertSame(initialConfigurationsFirstTime.get(i), current);
         }
         // Test the current configurations (first time with lazy computation)
         List<ISymbolicConfiguration> currentConfigurationsFirstTime = new ArrayList<ISymbolicConfiguration>(extractor.getConfigurationsCount());
         for (int i = 0; i < extractor.getConfigurationsCount(); i++) {
            ISymbolicConfiguration current = extractor.getCurrentConfiguration(i);
            currentConfigurationsFirstTime.add(current);
            String oracleFile = oraclePathInBaseDir + currentStatesOraclePrefix + i + currentStatesOracleFileExtension;
            createOracleFile(current, oracleFile);
            if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
               SymbolicConfigurationReader reader = new SymbolicConfigurationReader();
               ISymbolicConfiguration expected = reader.read(new File(keyRepDirectory, oracleFile));
               assertNotNull(expected);
               assertModel(expected, current);
            }
         }
         // Test the current configurations (second time with same configurations)
         for (int i = 0; i < extractor.getConfigurationsCount(); i++) {
            ISymbolicConfiguration current = extractor.getCurrentConfiguration(i);
            assertSame(currentConfigurationsFirstTime.get(i), current);
         }
      }
      finally {
         // Restore runtime option
         if (originalRuntimeExceptions != null) {
            SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalRuntimeExceptions);
         }
      }
   }
   
   /**
    * Compares the given {@link ISymbolicConfiguration}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   protected static void createOracleFile(ISymbolicConfiguration model, 
                                          String oraclePathInBaseDirFile) throws IOException, ProofInputException {
      if (tempNewOracleDirectory != null && tempNewOracleDirectory.isDirectory()) {
         // Create sub folder structure
         File oracleFile = new File(tempNewOracleDirectory, oraclePathInBaseDirFile);
         oracleFile.getParentFile().mkdirs();
         // Create oracle file
         SymbolicConfigurationWriter writer = new SymbolicConfigurationWriter();
         writer.write(model, SymbolicConfigurationWriter.DEFAULT_ENCODING, oracleFile);
         // Print message to the user.
         printOracleDirectory();
      }
   }
   
   public static void assertModel(ISymbolicConfiguration expected, ISymbolicConfiguration current) {
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
         assertListEquals(expected.getTermStrings(), current.getTermStrings());
         assertEquals(expected.getRepresentativeString(), current.getRepresentativeString());
      }
      else {
         assertNull(current);
      }
   }
   
   /**
    * Compares the given {@link ImmutableList}s.
    * @param expected The expected instance.
    * @param current The current instance.
    */
   public static <T> void assertListEquals(ImmutableList<T> expected, ImmutableList<T> current) {
      assertNotNull(expected);
      assertNotNull(current);
      assertEquals(expected.size(), current.size());
      Iterator<T> expectedIter = expected.iterator();
      Iterator<T> currentIter = current.iterator();
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         assertEquals(expectedIter.next(), currentIter.next());
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
         assertEquals(expected.getArrayIndex(), current.getArrayIndex());
         assertEquals(expected.getValueString(), current.getValueString());
         assertEquals(expected.getTypeString(), current.getTypeString());
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
         assertEquals(expected.getArrayIndex(), current.getArrayIndex());
         assertObject(expected.getTarget(), current.getTarget(), false);
      }
      else {
         assertNull(current);
      }
   }
}
