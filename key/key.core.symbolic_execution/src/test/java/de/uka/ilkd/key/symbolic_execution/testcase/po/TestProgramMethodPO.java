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

package de.uka.ilkd.key.symbolic_execution.testcase.po;

import java.io.IOException;
import java.util.HashMap;

import javax.xml.parsers.ParserConfigurationException;

import org.key_project.util.java.StringUtil;
import org.xml.sax.SAXException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import static org.junit.Assert.*;
import org.junit.Test;

/**
 * Tests for {@link ProgramMethodPO}.
 * @author Martin Hentschel
 */
public class TestProgramMethodPO extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests {@code complicatedMethod} without precondition.
    */
   @Test public void testComplicatedInnerMethod() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("/set/fullqualifiedTypeNamesTest/test/my/packageName/TheClass.java",
             "my.packageName.TheClass.TheInnerClass",
             "complicatedInnerMethod",
             "/set/fullqualifiedTypeNamesTest/oracle/TheInnerClass_complicatedInnerMethod.xml",
             null,
             "{result=self.complicatedInnerMethod(z,a,b,x,o,ac)@my.packageName.TheClass.TheInnerClass; }");
   }
   
   /**
    * Tests {@code complicatedMethod} with precondition.
    */
   @Test public void testComplicatedMethod_Precondition() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("/set/fullqualifiedTypeNamesTest/test/my/packageName/TheClass.java",
             "my.packageName.TheClass",
             "complicatedMethod",
             "/set/fullqualifiedTypeNamesTest/oracle/TheClass_complicatedMethod.xml",
             "a == 2 && b && x != null && \"Hello\" == x",
             "{result=self.complicatedMethod(i,a,b,x,o,ac,acArray)@my.packageName.TheClass; }");
   }
   
   /**
    * Tests {@code complicatedMethod} without precondition.
    */
   @Test public void testComplicatedMethod() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("/set/fullqualifiedTypeNamesTest/test/my/packageName/TheClass.java",
             "my.packageName.TheClass",
             "complicatedMethod",
             "/set/fullqualifiedTypeNamesTest/oracle/TheClass_complicatedMethod.xml",
             null,
             "{result=self.complicatedMethod(i,a,b,x,o,ac,acArray)@my.packageName.TheClass; }");
   }
   
   /**
    * Tests {@code returnMethod} with precondition.
    */
   @Test public void testReturnMethod_Precondition() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("/set/methodPOTest/test/MethodPOTest.java",
             "MethodPOTest",
             "returnMethod",
             "/set/methodPOTest/oracle/MethodPOTest_returnMethod_ParamNotNull.xml",
             "param != null",
             "{result=MethodPOTest.returnMethod(param)@MethodPOTest; }");
   }
   
   /**
    * Tests {@code returnMethod} without precondition.
    */
   @Test public void testReturnMethod() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("/set/methodPOTest/test/MethodPOTest.java",
             "MethodPOTest",
             "returnMethod",
             "/set/methodPOTest/oracle/MethodPOTest_returnMethod.xml",
             null,
             "{result=MethodPOTest.returnMethod(param)@MethodPOTest; }");
   }
   
   /**
    * Tests {@code voidMethod} with precondition.
    */
   @Test public void testVoidMethod_Precondition() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("/set/methodPOTest/test/MethodPOTest.java",
             "MethodPOTest",
             "voidMethod",
             "/set/methodPOTest/oracle/MethodPOTest_voidMethod_ParamNotNull.xml",
             "param != null",
             "{MethodPOTest.voidMethod(param)@MethodPOTest; }");
   }
   
   /**
    * Tests {@code voidMethod} without precondition.
    */
   @Test public void testVoidMethod() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("/set/methodPOTest/test/MethodPOTest.java",
             "MethodPOTest",
             "voidMethod",
             "/set/methodPOTest/oracle/MethodPOTest_voidMethod.xml",
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
      HashMap<String, String> originalTacletOptions = null;
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try {
         // Make sure that the correct taclet options are defined.
         originalTacletOptions = setDefaultTacletOptions(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName);
         setOneStepSimplificationEnabled(null, true);
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, precondition, false, false, false, false, false, false, false, false, false, true);
         // Extract and test try content
         String tryContent = getTryContent(env.getProof());
         assertTrue("Expected \"" + expectedTryContent + "\" but is \"" + tryContent + "\".", StringUtil.equalIgnoreWhiteSpace(expectedTryContent, tryContent));
         // Resume
         resume(env.getUi(), env.getBuilder(), oraclePathInBaseDirFile, testCaseDirectory);
         // Test save and reload of the proof
         assertSaveAndReload(testCaseDirectory, javaPathInkeyRepDirectory, oraclePathInBaseDirFile, env);
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
}