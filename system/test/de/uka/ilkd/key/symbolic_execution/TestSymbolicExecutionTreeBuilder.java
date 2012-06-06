package de.uka.ilkd.key.symbolic_execution;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.Properties;

import javax.xml.parsers.ParserConfigurationException;

import junit.framework.TestCase;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.po.SymbolicExecutionFunctionalOperationContractPO;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * <p>
 * Tests for {@link SymbolicExecutionTreeBuilder}.
 * </p>
 * <p>
 * This test needs access to the checkout of the KeY repository defined
 * via Java System Property {@code key.home}, e.g. via VM argument:
 * {@code -Dkey.home=D:\Forschung\GIT\KeY}
 * </p>
 * @author Martin Hentschel
 */
public class TestSymbolicExecutionTreeBuilder extends TestCase {
   /**
    * <p>
    * If this constant is {@code true} a temporary directory is created with
    * new oracle files. The developer has than to copy the new required files
    * into the plug-in so that they are used during next test execution.
    * </p>
    * <p>
    * <b>Attention: </b> It is strongly required that new test scenarios
    * are verified with the SED application. If everything is fine a new test
    * method can be added to this class and the first test execution can be
    * used to generate the required oracle file. Existing oracle files should
    * only be replaced if the functionality of the Symbolic Execution Debugger
    * has changed so that they are outdated.
    * </p>
    */
   public static final boolean CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY = false;
   
   /**
    * The used temporary oracle directory.
    */
   private static final File tempNewOracleDirectory;
   
   /**
    * The directory which contains the KeY repository.
    */
   private static final File keyRepDirectory;
   
   /**
    * Creates the temporary oracle directory if required.
    */
   static {
      // Create temporary director for oracle files if required.
      File directory = null;
      try {
         if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            directory = File.createTempFile("SYMBOLIC_EXECUTION", "ORACLE_DIRECTORY");
            directory.delete();
            directory.mkdirs();
         }
      }
      catch (IOException e) {
      }
      tempNewOracleDirectory = directory;
      // Detect the KeY repository.
      // By default the repository should be the current path.
      // But in Eclipse development like for the symbolic execution debugger it is the eclipse plug-in.
      File currentDirectory = null;
      try {
         // Try to get key home directory from system property
         String keyProp = System.getProperty("key.home");
         if (keyProp != null)  {
            currentDirectory = new File(keyProp);
         }
         // Try to get it from customTargets.properties if plug-in org.key_project.key4eclipse is used.
         if (currentDirectory == null || !currentDirectory.isDirectory()) {
            File customTargets = new File(currentDirectory, "customTargets.properties"); 
            if (customTargets.isFile()) {
               // Extract repository directory from properties.
               Properties properties = new Properties();
               Reader reader = new FileReader(customTargets);
               try {
                  properties.load(reader);
               }
               finally {
                  reader.close();
               }
               final String KEY_REP_KEY = "key.rep";
               assertTrue("Value \"" + KEY_REP_KEY + "\" is not defined in \"" + customTargets.getAbsolutePath() + "\".", properties.containsKey(KEY_REP_KEY));
               currentDirectory = new File(properties.getProperty(KEY_REP_KEY));
            }
         }
      }
      catch (IOException e) {
      }
      keyRepDirectory = currentDirectory;  
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesArrayTest
    */
   public void testVariablesArrayTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/variablesArrayTest/test/VariablesArrayTest.java", 
             "VariablesArrayTest", 
             "main", 
             "examples/_testcase/set/variablesArrayTest/oracle/VariablesArrayTest.xml",
             true);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesInstanceVariableTest
    */
   public void testVariablesInstanceVariableTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/variablesInstanceVariableTest/test/VariablesInstanceVariableTest.java", 
             "VariablesInstanceVariableTest", 
             "main", 
             "examples/_testcase/set/variablesInstanceVariableTest/oracle/VariablesInstanceVariableTest.xml",
             true);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesLocalTest
    */
   public void testVariablesLocalTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/variablesLocalTest/test/VariablesLocalTest.java", 
             "VariablesLocalTest", 
             "main", 
             "examples/_testcase/set/variablesLocalTest/oracle/VariablesLocalTest.xml",
             true);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesStaticTest
    */
   public void testVariablesStaticTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/variablesStaticTest/test/VariablesStaticTest.java", 
             "VariablesStaticTest", 
             "main", 
             "examples/_testcase/set/variablesStaticTest/oracle/VariablesStaticTest.xml",
             true);
   }
   
   /**
    * Tests example: examples/_testcase/set/complexFlatSteps
    */
   public void testComplexFlatSteps() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/complexFlatSteps/test/ComplexFlatSteps.java", 
             "ComplexFlatSteps", 
             "doSomething", 
             "examples/_testcase/set/complexFlatSteps/oracle/ComplexFlatSteps.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/complexIf
    */
   public void testComplexIf() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/complexIf/test/ComplexIf.java", 
             "ComplexIf", 
             "min", 
             "examples/_testcase/set/complexIf/oracle/ComplexIf.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/doWhileFalseTest
    */
   public void testDoWhileFlaseTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/doWhileFalseTest/test/DoWhileFalseTest.java", 
             "DoWhileFalseTest", 
             "main", 
             "examples/_testcase/set/doWhileFalseTest/oracle/DoWhileFalseTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/doWhileTest
    */
   public void testDoWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/doWhileTest/test/DoWhileTest.java", 
             "DoWhileTest", 
             "main", 
             "examples/_testcase/set/doWhileTest/oracle/DoWhileTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/elseIfDifferentVariables
    */
   public void testElseIfDifferentVariables() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/elseIfDifferentVariables/test/ElseIfDifferentVariables.java", 
             "ElseIfDifferentVariables", 
             "main", 
             "examples/_testcase/set/elseIfDifferentVariables/oracle/ElseIfDifferentVariables.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/elseIfTest
    */
   public void testElseIfTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/elseIfTest/test/ElseIfTest.java", 
             "ElseIfTest", 
             "elseIf", 
             "examples/_testcase/set/elseIfTest/oracle/ElseIfTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/fixedRecursiveMethodCallTest
    */
   public void testFixedRecursiveMethodCallTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/fixedRecursiveMethodCallTest/test/FixedRecursiveMethodCallTest.java", 
             "FixedRecursiveMethodCallTest", 
             "decreaseValue", 
             "examples/_testcase/set/fixedRecursiveMethodCallTest/oracle/FixedRecursiveMethodCallTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/forEachTest
    */
   public void testForEachTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/forEachTest/test/ForEachTest.java", 
             "ForEachTest", 
             "main", 
             "examples/_testcase/set/forEachTest/oracle/ForEachTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/forFalseTest
    */
   public void testForFalseTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/forFalseTest/test/ForFalseTest.java", 
             "ForFalseTest", 
             "main", 
             "examples/_testcase/set/forFalseTest/oracle/ForFalseTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/forTest
    */
   public void testForTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/forTest/test/ForTest.java", 
             "ForTest", 
             "main", 
             "examples/_testcase/set/forTest/oracle/ForTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalDoWhileTest
    */
   public void testFunctionalDoWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/functionalDoWhileTest/test/FunctionalDoWhileTest.java", 
             "FunctionalDoWhileTest", 
             "main", 
             "examples/_testcase/set/functionalDoWhileTest/oracle/FunctionalDoWhileTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalForTest
    */
   public void testFunctionalForTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/functionalForTest/test/FunctionalForTest.java", 
             "FunctionalForTest", 
             "main", 
             "examples/_testcase/set/functionalForTest/oracle/FunctionalForTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalIf
    */
   public void testFunctionalIf() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/functionalIf/test/FunctionalIf.java", 
             "FunctionalIf", 
             "min", 
             "examples/_testcase/set/functionalIf/oracle/FunctionalIf.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalWhileTest
    */
   public void testFunctionalWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/functionalWhileTest/test/FunctionalWhileTest.java", 
             "FunctionalWhileTest", 
             "main", 
             "examples/_testcase/set/functionalWhileTest/oracle/FunctionalWhileTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallOnObject
    */
   public void testMethodCallOnObject() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodCallOnObject/test/MethodCallOnObject.java", 
             "MethodCallOnObject", 
             "main", 
             "examples/_testcase/set/methodCallOnObject/oracle/MethodCallOnObject.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallOnObjectWithException
    */
   public void testMethodCallOnObjectWithException() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodCallOnObjectWithException/test/MethodCallOnObjectWithException.java", 
             "MethodCallOnObjectWithException", 
             "main", 
             "examples/_testcase/set/methodCallOnObjectWithException/oracle/MethodCallOnObjectWithException.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallParallelTest
    */
   public void testMethodCallParallelTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodCallParallelTest/test/MethodCallParallelTest.java", 
             "MethodCallParallelTest", 
             "main", 
             "examples/_testcase/set/methodCallParallelTest/oracle/MethodCallParallelTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodFormatTest
    */
   public void testMethodFormatTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodFormatTest/test/MethodFormatTest.java", 
             "MethodFormatTest", 
             "main", 
             "examples/_testcase/set/methodFormatTest/oracle/MethodFormatTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodHierarchyCallTest
    */
   public void testMethodHierarchyCallTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodHierarchyCallTest/test/MethodHierarchyCallTest.java", 
             "MethodHierarchyCallTest", 
             "main", 
             "examples/_testcase/set/methodHierarchyCallTest/oracle/MethodHierarchyCallTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodHierarchyCallWithExceptionTest
    */
   public void testMethodHierarchyCallWithExceptionTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodHierarchyCallWithExceptionTest/test/MethodHierarchyCallWithExceptionTest.java", 
             "MethodHierarchyCallWithExceptionTest", 
             "main", 
             "examples/_testcase/set/methodHierarchyCallWithExceptionTest/oracle/MethodHierarchyCallWithExceptionTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedDoWhileTest
    */
   public void testNestedDoWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/nestedDoWhileTest/test/NestedDoWhileTest.java", 
             "NestedDoWhileTest", 
             "main", 
             "examples/_testcase/set/nestedDoWhileTest/oracle/NestedDoWhileTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedForTest
    */
   public void testNestedForTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/nestedForTest/test/NestedForTest.java", 
             "NestedForTest", 
             "main", 
             "examples/_testcase/set/nestedForTest/oracle/NestedForTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedWhileTest
    */
   public void testNestedWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/nestedWhileTest/test/NestedWhileTest.java", 
             "NestedWhileTest", 
             "mainNested", 
             "examples/_testcase/set/nestedWhileTest/oracle/NestedWhileTest.xml",
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
      doTest(keyRepDirectory, 
             "examples/_testcase/set/recursiveFibonacci/test/RecursiveFibonacci.java", 
             "RecursiveFibonacci", 
             "fibonacci10", 
             "examples/_testcase/set/recursiveFibonacci/oracle/RecursiveFibonacci.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleIf
    */
   public void testSimpleIf() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/simpleIf/test/SimpleIf.java", 
             "SimpleIf", 
             "min", 
             "examples/_testcase/set/simpleIf/oracle/SimpleIf.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleNullPointerSplitTest
    */
   public void testSimpleNullPointerSplitTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/simpleNullPointerSplitTest/test/SimpleNullPointerSplitTest.java", 
             "SimpleNullPointerSplitTest", 
             "main", 
             "examples/_testcase/set/simpleNullPointerSplitTest/oracle/SimpleNullPointerSplitTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/statementKindTest
    */
   public void testStatementKindTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/statementKindTest/test/StatementKindTest.java", 
             "StatementKindTest", 
             "main", 
             "examples/_testcase/set/statementKindTest/oracle/StatementKindTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/statements
    */
   public void testStatements() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/statements/test/FlatSteps.java", 
             "FlatSteps", 
             "doSomething", 
             "examples/_testcase/set/statements/oracle/FlatSteps.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticMethodCall
    */
   public void testStaticMethodCall() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/staticMethodCall/test/StaticMethodCall.java", 
             "StaticMethodCall", 
             "main", 
             "examples/_testcase/set/staticMethodCall/oracle/StaticMethodCall.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/switchCaseTest
    */
   public void testSwitchCaseTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/switchCaseTest/test/SwitchCaseTest.java", 
             "SwitchCaseTest", 
             "switchCase", 
             "examples/_testcase/set/switchCaseTest/oracle/SwitchCaseTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/throwTest
    */
   public void testThrowTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/throwTest/test/ThrowTest.java", 
             "ThrowTest", 
             "main", 
             "examples/_testcase/set/throwTest/oracle/ThrowTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/throwVariableTest
    */
   public void testThrowVariableTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/throwVariableTest/test/ThrowVariableTest.java", 
             "ThrowVariableTest", 
             "main", 
             "examples/_testcase/set/throwVariableTest/oracle/ThrowVariableTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/tryCatchFinally
    */
   public void testTryCatchFinally() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/tryCatchFinally/test/TryCatchFinally.java", 
             "TryCatchFinally", 
             "tryCatchFinally", 
             "examples/_testcase/set/tryCatchFinally/oracle/TryCatchFinally.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/whileFalseTest
    */
   public void testWhileFalseTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/whileFalseTest/test/WhileFalseTest.java", 
             "WhileFalseTest", 
             "main", 
             "examples/_testcase/set/whileFalseTest/oracle/WhileFalseTest.xml",
             false);
   }
   
   /**
    * Tests example: examples/_testcase/set/whileTest
    */
   public void testWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/whileTest/test/WhileTest.java", 
             "WhileTest", 
             "main", 
             "examples/_testcase/set/whileTest/oracle/WhileTest.xml",
             false);
   }
   
   /**
    * Executes a test with the following steps:
    * <ol>
    *    <li>Load java file</li>
    *    <li>Instantiate proof for method in container type</li>
    *    <li>Try to close proof in auto mode</li>
    *    <li>Create symbolic execution tree</li>
    *    <li>Create new oracle file in temporary directory {@link #tempNewOracleDirectory} if it is defined</li>
    *    <li>Load oracle file</li>
    *    <li>Compare created symbolic execution tree with oracle model</li>
    * </ol>
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The java class to test.
    * @param methodFullName The method to test.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @param includeVariables Include variables?
    * @throws ProofInputException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected void doTest(File baseDir,
                         String javaPathInBaseDir,
                         String containerTypeName,
                         final String methodFullName,
                         String oraclePathInBaseDirFile,
                         boolean includeVariables) throws ProofInputException, IOException, ParserConfigurationException, SAXException {
      // Make sure that parameter are valid.
      assertNotNull(javaPathInBaseDir);
      File javaFile = new File(baseDir, javaPathInBaseDir);
      assertTrue(javaFile.exists());
      assertNotNull(containerTypeName);
      assertNotNull(methodFullName);
      assertNotNull(oraclePathInBaseDirFile);
      File oracleFile = new File(baseDir, oraclePathInBaseDirFile);
      if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
         assertTrue("Oracle file does not exist. Set \"CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY\" to true to create an oracle file.", oracleFile.exists());
      }
      // Create user interface
      CustomConsoleUserInterface ui = new CustomConsoleUserInterface(false);
      // Load java file
      InitConfig initConfig = ui.load(javaFile, null, null);
      // Search method to proof
      Services services = initConfig.getServices();
      JavaInfo javaInfo = services.getJavaInfo();
      KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
      assertNotNull(containerKJT);
      ImmutableList<ProgramMethod> pms = javaInfo.getAllProgramMethods(containerKJT);
      ProgramMethod pm = JavaUtil.search(pms, new IFilter<ProgramMethod>() {
         @Override
         public boolean select(ProgramMethod element) {
            return methodFullName.equals(element.getFullName());
         }
      });
      assertNotNull(pm);
      // Create default contract for method to test
      FunctionalOperationContract contract = SymbolicExecutionUtil.createDefaultContract(services, pm);
      // Start proof
      ProofOblInput input = new SymbolicExecutionFunctionalOperationContractPO(initConfig, (FunctionalOperationContract)contract);
      Proof proof = ui.createProof(initConfig, input);
      assertNotNull(proof);
      // Set strategy to use for auto mode
      StrategyProperties strategyProperties = SymbolicExecutionStrategy.getSymbolicExecutionStrategyProperties(true, false, false, true);
      proof.setActiveStrategy(new SymbolicExecutionStrategy.Factory().create(proof, strategyProperties));
      // Run proof
      ui.startAndWaitForProof(proof);
      // Create symbolic execution tree
      SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(proof);
      builder.analyse();
      assertNotNull(builder.getStartNode());
      // Create new oracle file if required in a temporary directory
      createOracleFile(builder.getStartNode(), oraclePathInBaseDirFile, includeVariables);
      // Read oracle file
      ExecutionNodeReader reader = new ExecutionNodeReader();
      IExecutionNode oracleRoot = reader.read(oracleFile);
      assertNotNull(oracleRoot);
      // Make sure that the created symbolic execution tree matches the expected one.
      assertExecutionNodes(oracleRoot, builder.getStartNode(), includeVariables);
   }
   
   /**
    * Creates a new oracle file.
    * @param node The node to save as oracle file.
    * @param oraclePathInBaseDirFile The path in example directory.
    * @param saveVariables Save variables?
    * @throws IOException Occurred Exception
    * @throws ProofInputException Occurred Exception
    */
   protected void createOracleFile(IExecutionNode node, String oraclePathInBaseDirFile, boolean saveVariables) throws IOException, ProofInputException {
      if (tempNewOracleDirectory != null && tempNewOracleDirectory.isDirectory()) {
         // Create sub folder structure
         File oracleFile = new File(tempNewOracleDirectory, oraclePathInBaseDirFile);
         oracleFile.getParentFile().mkdirs();
         // Create oracle file
         ExecutionNodeWriter writer = new ExecutionNodeWriter();
         writer.write(node, ExecutionNodeWriter.DEFAULT_ENCODING, oracleFile, saveVariables);
         // Print message to the user.
         printOracleDirectory();
      }
   }
   
   /**
    * Prints {@link #tempNewOracleDirectory} to the user via {@link System#out}.
    */
   protected void printOracleDirectory() {
      if (tempNewOracleDirectory != null) {
         final String HEADER_LINE = "Oracle Directory is:";
         final String PREFIX = "### ";
         final String SUFFIX = " ###";
         String path = tempNewOracleDirectory.toString();
         int length = Math.max(path.length(), HEADER_LINE.length());
         String borderLines = JavaUtil.createLine("#", PREFIX.length() + length + SUFFIX.length());
         System.out.println(borderLines);
         System.out.println(PREFIX + HEADER_LINE + JavaUtil.createLine(" ", length - HEADER_LINE.length()) + SUFFIX);
         System.out.println(PREFIX + path + JavaUtil.createLine(" ", length - path.length()) + SUFFIX);
         System.out.println(borderLines);
      }
   }

   /**
    * Makes sure that the given nodes and their subtrees contains the same content.
    * @param expected The expected {@link IExecutionNode}.
    * @param current The current {@link IExecutionNode}.
    * @param compareVariables Compare variables?
    * @throws ProofInputException Occurred Exception.
    */
   public static void assertExecutionNodes(IExecutionNode expected, 
                                           IExecutionNode current,
                                           boolean compareVariables) throws ProofInputException {
      ExecutionNodePreorderIterator expectedIter = new ExecutionNodePreorderIterator(expected);
      ExecutionNodePreorderIterator currentIter = new ExecutionNodePreorderIterator(current);
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         IExecutionNode expectedNext = expectedIter.next();
         IExecutionNode currentNext = currentIter.next();
         assertExecutionNode(expectedNext, currentNext, true, true, compareVariables);
      }
      assertFalse(expectedIter.hasNext());
      assertFalse(currentIter.hasNext());
   }
   
   /**
    * Makes sure that the given nodes contains the same content.
    * Children are not compared.
    * @param expected The expected {@link IExecutionNode}.
    * @param current The current {@link IExecutionNode}.
    * @param compareParent Compare also the parent node?
    * @param compareChildren Compare direct children?
    * @param compareVariables Compare variables?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertExecutionNode(IExecutionNode expected, 
                                             IExecutionNode current, 
                                             boolean compareParent, 
                                             boolean compareChildren,
                                             boolean compareVariables) throws ProofInputException {
      // Compare nodes
      assertNotNull(expected);
      assertNotNull(current);
      assertEquals(expected.getName(), current.getName());
      assertEquals(expected.getFormatedPathCondition(), current.getFormatedPathCondition());
      if (expected instanceof IExecutionBranchCondition) {
         assertTrue("Expected IExecutionBranchCondition but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionBranchCondition);
         assertEquals(((IExecutionBranchCondition)expected).getFormatedBranchCondition(), ((IExecutionBranchCondition)current).getFormatedBranchCondition());
      }
      else if (expected instanceof IExecutionStartNode) {
         assertTrue("Expected IExecutionStartNode but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionStartNode);
      }
      else if (expected instanceof IExecutionTermination) {
         assertTrue("Expected IExecutionTermination but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionTermination);
         assertEquals(((IExecutionTermination)expected).isExceptionalTermination(), ((IExecutionTermination)current).isExceptionalTermination());
      }
      else if (expected instanceof IExecutionBranchNode) {
         assertTrue("Expected IExecutionBranchNode but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionBranchNode);
         assertVariables((IExecutionBranchNode)expected, (IExecutionBranchNode)current, compareVariables);
      }
      else if (expected instanceof IExecutionLoopCondition) {
         assertTrue("Expected IExecutionLoopCondition but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionLoopCondition);
         assertVariables((IExecutionLoopCondition)expected, (IExecutionLoopCondition)current, compareVariables);
      }
      else if (expected instanceof IExecutionLoopNode) {
         assertTrue("Expected IExecutionLoopNode but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionLoopNode);
         assertVariables((IExecutionLoopNode)expected, (IExecutionLoopNode)current, compareVariables);
      }
      else if (expected instanceof IExecutionMethodCall) {
         assertTrue("Expected IExecutionMethodCall but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionMethodCall);
         assertVariables((IExecutionMethodCall)expected, (IExecutionMethodCall)current, compareVariables);
      }
      else if (expected instanceof IExecutionMethodReturn) {
         assertTrue("Expected IExecutionMethodReturn but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionMethodReturn);
         assertTrue(((IExecutionMethodReturn)expected).getNameIncludingReturnValue() + " does not match " + ((IExecutionMethodReturn)current).getNameIncludingReturnValue(), JavaUtil.equalIgnoreWhiteSpace(((IExecutionMethodReturn)expected).getNameIncludingReturnValue(), ((IExecutionMethodReturn)current).getNameIncludingReturnValue()));
         assertVariables((IExecutionMethodReturn)expected, (IExecutionMethodReturn)current, compareVariables);
      }
      else if (expected instanceof IExecutionStatement) {
         assertTrue("Expected IExecutionStatement but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionStatement);
         assertVariables((IExecutionStatement)expected, (IExecutionStatement)current, compareVariables);
      }
      else {
         fail("Unknown execution node \"" + expected + "\".");
      }
      // Optionally compare parent
      if (compareParent) {
         assertExecutionNode(expected, current, false, false, compareVariables);
      }
      // Optionally compare direct children
      if (compareChildren) {
         IExecutionNode[] expectedChildren = expected.getChildren();
         IExecutionNode[] currentChildren = current.getChildren();
         assertEquals(expectedChildren.length, currentChildren.length);
         for (int i = 0; i < expectedChildren.length; i++) {
            assertExecutionNode(expectedChildren[i], currentChildren[i], false, false, compareVariables);
         }
      }
   }

   /**
    * Makes sure that the given nodes contains the same {@link IExecutionVariable}s.
    * @param expected The expected node.
    * @param current The current node.
    * @param compareVariables Compare variables?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertVariables(IExecutionStateNode<?> expected, IExecutionStateNode<?> current, boolean compareVariables) throws ProofInputException {
      if (compareVariables) {
         assertNotNull(expected);
         assertNotNull(current);
         IExecutionVariable[] expectedVariables = expected.getVariables();
         IExecutionVariable[] currentVariables = current.getVariables();
         assertEquals(expectedVariables.length, currentVariables.length);
         for (int i = 0; i < expectedVariables.length; i++) {
            assertVariable(expectedVariables[i], currentVariables[i], true, true);
         }
      }
   }

   /**
    * Makes sure that the given variables are the same.
    * @param expected The expected variable.
    * @param current The current variable.
    * @param compareParent Compare parent?
    * @param compareChildren Compare children?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertVariable(IExecutionVariable expected, 
                                        IExecutionVariable current,
                                        boolean compareParent, 
                                        boolean compareChildren) throws ProofInputException {
      if (expected != null) {
         assertNotNull(current);
         // Compare variable
         assertEquals(expected.isArrayIndex(), current.isArrayIndex());
         assertEquals(expected.getArrayIndex(), current.getArrayIndex());
         assertEquals(expected.getName(), current.getName());
         assertEquals(expected.getTypeString(), current.getTypeString());
         assertTrue(expected.getValueString() + " does not match " + current.getValueString(), JavaUtil.equalIgnoreWhiteSpace(expected.getValueString(), current.getValueString()));
         // Compare parent
         if (compareParent) {
            assertVariable(expected.getParentVariable(), current.getParentVariable(), false, false);
         }
         // Compare children
         if (compareChildren) {
            IExecutionVariable[] expectedChildVariables = expected.getChildVariables();
            IExecutionVariable[] currentChildVariables = current.getChildVariables();
            assertEquals(expectedChildVariables.length, currentChildVariables.length);
            for (int i = 0; i < expectedChildVariables.length; i++) {
               assertVariable(expectedChildVariables[i], currentChildVariables[i], compareParent, compareChildren);
            }
         }
      }
      else {
         assertNull(current);
      }
   }
}
