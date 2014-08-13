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

package de.uka.ilkd.key.symbolic_execution.po;

import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Tests for {@link ProgramMethodSubsetPO}.
 * @author Martin Hentschel
 */
public class TestProgramMethodSubsetPO extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests {@code x-=42;return x;} of {@code doSomething} with precondition.
    */
   public void testDoSomethingElseBranch() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "doSomething",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_elsebranch.xml",
             null,
             new Position(24, 27),
             new Position(25, 33),
             "{method-frame(result->result, source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self): { x-=42;return x; } }");
   }

   /**
    * Tests {@code x=x*-1; x+=2;} of {@code doSomething} with precondition.
    */
   public void testDoSomethingIfBranch() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "doSomething",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_ifbranch.xml",
             null,
             new Position(20, 27),
             new Position(21, 31),
             "{method-frame(source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self): { x=x*-1; x+=2; } }");
   }
   
   /**
    * Tests {@code {method-frame(source=doSomething(int, String, boolean)@MethodPartPOTest,this=self): {if (asdf<0) {
    * x=x*-1;
    * x+=2;
    * }else  {
    * x-=42;return x;
    * }
    * }
    * }} of {@code doSomething} with precondition.
    */
   public void testDoSomethingIf() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "doSomething",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_if.xml",
             null,
             new Position(19, 17),
             new Position(26, 17),
             "{method-frame(source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self): {if (asdf<0) { x=x*-1; x+=2; }else  { x-=42;return x; } } }");
   }
   
   /**
    * Tests {@code {method-frame(source=doSomething(int, String, boolean)@MethodPartPOTest,this=self): {int x = 0;if (asdf<0) {
    * x=x*-1;
    * x+=2;
    * }else  {
    * x-=42;return x;
    * }
    * x=1*asdf;
    * }
    * }} of {@code doSomething} with precondition.
    */
   public void testDoSomethingIfWithSurroundingStatements() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "doSomething",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_if_surroundingStatements.xml",
             null,
             new Position(17, 63),
             new Position(27, 29),
             "{method-frame(source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self): {int x = 0;if (asdf<0) { x=x*-1; x+=2; }else  { x-=42;return x; } x=1*asdf; } }");
   }
   
   /**
    * Tests {@code x=1*asdf;int y = 2+CONSTANT+field;int doubleValue = doubleValue(x);int z = x+y+doubleValue; return z;} of {@code doSomething} with precondition.
    */
   public void testDoSomethingWithReturn_Precondition() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "doSomething",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_withReturn_precondition.xml",
             "x == 1 && asdf == 2 && this.field == 3",
             new Position(27, 19),
             new Position(31, 25),
             "{method-frame(result->result, source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self): { x=1*asdf;int y = 2+MethodPartPOTest.CONSTANT+this.field;int doubleValue = doubleValue(x);int z = x+y+doubleValue;return z; } }");
   }
   
   /**
    * Tests {@code x=1*asdf;int y = 2+CONSTANT+field;int doubleValue = doubleValue(x);int z = x+y+doubleValue; return z;} of {@code doSomething} without precondition.
    */
   public void testDoSomethingWithReturn() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "doSomething",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_withReturn.xml",
             null,
             new Position(27, 19),
             new Position(31, 25),
             "{method-frame(result->result, source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self): { x=1*asdf;int y = 2+MethodPartPOTest.CONSTANT+this.field;int doubleValue = doubleValue(x);int z = x+y+doubleValue;return z; } }");
   }

   /**
    * Tests {@code x=1*asdf;int y = 2+CONSTANT+field;int doubleValue = doubleValue(x);int z = x+y+doubleValue;} of {@code doSomething} with precondition.
    */
   public void testDoSomethingNoReturn_Precondition() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "doSomething",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_noReturn_precondition.xml",
             "x == 1 && asdf == 2 && this.field == 3",
             new Position(27, 19),
             new Position(30, 44),
             "{method-frame(source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self): { x=1*asdf;int y = 2+MethodPartPOTest.CONSTANT+this.field;int doubleValue = doubleValue(x);int z = x+y+doubleValue; } }");
   }
   
   /**
    * Tests {@code x=1*asdf;int y = 2+CONSTANT+field;int doubleValue = doubleValue(x);int z = x+y+doubleValue;} of {@code doSomething} without precondition.
    */
   public void testDoSomethingNoReturn() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "doSomething",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_doSomething_noReturn.xml",
             null,
             new Position(27, 19),
             new Position(30, 44),
             "{method-frame(source=doSomething(int, java.lang.String, boolean)@MethodPartPOTest,this=self): { x=1*asdf;int y = 2+MethodPartPOTest.CONSTANT+this.field;int doubleValue = doubleValue(x);int z = x+y+doubleValue; } }");
   }
   
   /**
    * Tests {@code int b = 3*y;return ;} of {@code voidMethod} with precondition.
    */
   public void testVoidMethodWithReturn_Precondition() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "voidMethod",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_voidMethod_withReturn_precondition.xml",
             "y == -2",
             new Position(11, 22),
             new Position(13, 31),
             "{method-frame(source=voidMethod(boolean, int)@MethodPartPOTest,this=self): {int b = 3*y;return ; } }");
   }
   
   /**
    * Tests {@code int b = 3*y;return ;} of {@code voidMethod} without precondition.
    */
   public void testVoidMethodWithReturn() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "voidMethod",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_voidMethod_withReturn.xml",
             null,
             new Position(11, 22),
             new Position(13, 31),
             "{method-frame(source=voidMethod(boolean, int)@MethodPartPOTest,this=self): {int b = 3*y;return ; } }");
   }
   
   /**
    * Tests {@code int a = 2 * y;} of {@code voidMethod} with precondition.
    */
   public void testVoidMethodNoReturn_Precondition() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "voidMethod",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_voidMethod_noReturn_precondition.xml",
             "y == 2",
             new Position(8, 24),
             new Position(9, 38),
             "{method-frame(source=voidMethod(boolean, int)@MethodPartPOTest,this=self): {int a = 2*y; } }");
   }
   
   /**
    * Tests {@code int a = 2 * y;} of {@code voidMethod} without precondition.
    */
   public void testVoidMethodNoReturn() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/methodPartPOTest/test/MethodPartPOTest.java",
             "MethodPartPOTest",
             "voidMethod",
             "examples/_testcase/set/methodPartPOTest/oracle/MethodPartPOTest_voidMethod_noReturn.xml",
             null,
             new Position(8, 24),
             new Position(9, 38),
             "{method-frame(source=voidMethod(boolean, int)@MethodPartPOTest,this=self): {int a = 2*y; } }");
   }
   
   /**
    * Executes the test steps of all contained test methods.
    */
   protected void doTest(String javaPathInkeyRepDirectory,
                         String containerTypeName,
                         String methodFullName,
                         String oraclePathInBaseDirFile,
                         String precondition,
                         Position startPosition,
                         Position endPosition,
                         String expectedTryContent) throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      // Create proof environment for symbolic execution
      SymbolicExecutionEnvironment<CustomUserInterface> env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, precondition, startPosition, endPosition, false, false, false, false, false, false, false);
      try {
         // Extract and test try content
         String tryContent = getTryContent(env.getProof());
         assertTrue("Expected \"" + expectedTryContent + "\" but is \"" + tryContent + "\".", JavaUtil.equalIgnoreWhiteSpace(expectedTryContent, tryContent));
         // Resume
         resume(env.getUi(), env.getBuilder(), oraclePathInBaseDirFile, keyRepDirectory);
         // Test save and reload of the proof
         assertSaveAndReload(keyRepDirectory, javaPathInkeyRepDirectory, oraclePathInBaseDirFile, env);
      }
      finally {
         env.dispose();
      }
   }
}