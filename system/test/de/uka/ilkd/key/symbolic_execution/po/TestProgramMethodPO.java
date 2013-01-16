package de.uka.ilkd.key.symbolic_execution.po;

import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Tests for {@link ProgramMethodPO}.
 * @author Martin Hentschel
 */
public class TestProgramMethodPO extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests {@code complicatedMethod} without precondition.
    */
   public void testComplicatedInnerMethod() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/fullqualifiedTypeNamesTest/test/my/packageName/TheClass.java",
             "TheInnerClass",
             "complicatedInnerMethod",
             "examples/_testcase/set/fullqualifiedTypeNamesTest/oracle/TheInnerClass_complicatedInnerMethod.xml",
             null,
             "{result=self.complicatedInnerMethod(z,a,b,x,o,ac)@my.packageName.TheClass.TheInnerClass; }");
   }
   
   /**
    * Tests {@code complicatedMethod} with precondition.
    */
   public void testComplicatedMethod_Precondition() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/fullqualifiedTypeNamesTest/test/my/packageName/TheClass.java",
             "TheClass",
             "complicatedMethod",
             "examples/_testcase/set/fullqualifiedTypeNamesTest/oracle/TheClass_complicatedMethod.xml",
             "a == 2 && b && x != null && \"Hello\" == x",
             "{result=self.complicatedMethod(i,a,b,x,o,ac,acArray)@my.packageName.TheClass; }");
   }
   
   /**
    * Tests {@code complicatedMethod} without precondition.
    */
   public void testComplicatedMethod() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/fullqualifiedTypeNamesTest/test/my/packageName/TheClass.java",
             "TheClass",
             "complicatedMethod",
             "examples/_testcase/set/fullqualifiedTypeNamesTest/oracle/TheClass_complicatedMethod.xml",
             null,
             "{result=self.complicatedMethod(i,a,b,x,o,ac,acArray)@my.packageName.TheClass; }");
   }
   
   /**
    * Tests {@code returnMethod} with precondition.
    */
   public void testReturnMethod_Precondition() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPOTest/test/MethodPOTest.java",
             "MethodPOTest",
             "returnMethod",
             "examples/_testcase/set/methodPOTest/oracle/MethodPOTest_returnMethod_ParamNotNull.xml",
             "param != null",
             "{result=MethodPOTest.returnMethod(param)@MethodPOTest; }");
   }
   
   /**
    * Tests {@code returnMethod} without precondition.
    */
   public void testReturnMethod() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPOTest/test/MethodPOTest.java",
             "MethodPOTest",
             "returnMethod",
             "examples/_testcase/set/methodPOTest/oracle/MethodPOTest_returnMethod.xml",
             null,
             "{result=MethodPOTest.returnMethod(param)@MethodPOTest; }");
   }
   
   /**
    * Tests {@code voidMethod} with precondition.
    */
   public void testVoidMethod_Precondition() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPOTest/test/MethodPOTest.java",
             "MethodPOTest",
             "voidMethod",
             "examples/_testcase/set/methodPOTest/oracle/MethodPOTest_voidMethod_ParamNotNull.xml",
             "param != null",
             "{MethodPOTest.voidMethod(param)@MethodPOTest; }");
   }
   
   /**
    * Tests {@code voidMethod} without precondition.
    */
   public void testVoidMethod() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPOTest/test/MethodPOTest.java",
             "MethodPOTest",
             "voidMethod",
             "examples/_testcase/set/methodPOTest/oracle/MethodPOTest_voidMethod.xml",
             null,
             "{MethodPOTest.voidMethod(param)@MethodPOTest; }");
   }
   
   /**
    * Executes the test steps of all contained test methods.
    */
   protected void doTest(String javaPathInkeyRepDirectory,
                         String containerTypeName,
                         String methodFullName,
                         String oraclePathInBaseDirFile,
                         String precondition,
                         String expectedTryContent) throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      String originalRuntimeExceptions = null;
      try {
         // Store original settings of KeY which requires that at least one proof was instantiated.
         if (!SymbolicExecutionUtil.isChoiceSettingInitialised()) {
            createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, precondition, false, false);
         }
         originalRuntimeExceptions = SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);
         assertNotNull(originalRuntimeExceptions);
         SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW);
         // Create proof environment for symbolic execution
         SymbolicExecutionEnvironment<CustomConsoleUserInterface> env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, precondition, false, false);
         // Extract and test try content
         String tryContent = getTryContent(env.getProof());
         assertTrue("Expected \"" + expectedTryContent + "\" but is \"" + tryContent + "\".", JavaUtil.equalIgnoreWhiteSpace(expectedTryContent, tryContent));
         // Resume
         resume(env.getUi(), env.getBuilder(), oraclePathInBaseDirFile, keyRepDirectory);
         // Test save and reload of the proof
         assertSaveAndReload(keyRepDirectory, javaPathInkeyRepDirectory, oraclePathInBaseDirFile, env);
      }
      finally {
         // Restore runtime option
         if (originalRuntimeExceptions != null) {
            SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalRuntimeExceptions);
         }
      }
   }
}
