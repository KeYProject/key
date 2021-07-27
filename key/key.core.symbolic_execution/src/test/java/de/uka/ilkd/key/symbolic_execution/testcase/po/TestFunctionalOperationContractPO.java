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
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import static org.junit.Assert.*;
import org.junit.Test;

/**
 * Tests the {@link FunctionalOperationContractPO} used for symbolic execution.
 * @author Martin Hentschel
 */
public class TestFunctionalOperationContractPO extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests the contract of method {@code doubleValue}.
    */
   @Test public void testDoubleValue() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("/set/existingContractTest/test/ExistingContractTest.java",
             "ExistingContractTest[ExistingContractTest::doubleValue(int)].JML operation contract.0",
             "/set/existingContractTest/oracle/ExistingContractTest.xml",
             "{result=self.doubleValue(_value)@ExistingContractTest; }");
   }
   
   /**
    * Executes the test steps of all contained test methods.
    */
   protected void doTest(String javaPathInkeyRepDirectory,
                         String baseContractName,
                         String oraclePathInBaseDirFile,
                         String expectedTryContent) throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      HashMap<String, String> originalTacletOptions = null;
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
      try {
         // Make sure that the correct taclet options are defined.
         originalTacletOptions = setDefaultTacletOptions(testCaseDirectory, javaPathInkeyRepDirectory, baseContractName);
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory, baseContractName, false, false, false, false, false, false, false, false, false, false, false);
         // Extract and test try content
         String tryContent = getTryContent(env.getProof());
         if (!StringUtil.equalIgnoreWhiteSpace(expectedTryContent, tryContent)) {
            assertEquals(expectedTryContent, tryContent);
         }
         // Resume
         resume(env.getUi(), env.getBuilder(), oraclePathInBaseDirFile, testCaseDirectory);
         // Test save and reload of the proof
         assertSaveAndReload(testCaseDirectory, javaPathInkeyRepDirectory, oraclePathInBaseDirFile, env);
      }
      finally {
         // Restore taclet options
         restoreTacletOptions(originalTacletOptions);
         if (env != null) {
            env.dispose();
         }
      }
   }
}