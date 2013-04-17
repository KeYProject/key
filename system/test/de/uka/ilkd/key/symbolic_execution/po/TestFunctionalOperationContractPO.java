// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
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

import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Tests the {@link FunctionalOperationContractPO} used for symbolic execution.
 * @author Martin Hentschel
 */
public class TestFunctionalOperationContractPO extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests the contract of method {@code doubleValue}.
    */
   public void testDoubleValue() throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      doTest("examples/_testcase/set/existingContractTest/test/ExistingContractTest.java",
             "ExistingContractTest[ExistingContractTest::doubleValue(int)].JML operation contract.0",
             "examples/_testcase/set/existingContractTest/oracle/ExistingContractTest.xml",
             "{result=self.doubleValue(_value)@ExistingContractTest; }");
   }
   
   /**
    * Executes the test steps of all contained test methods.
    */
   protected void doTest(String javaPathInkeyRepDirectory,
                         String baseContractName,
                         String oraclePathInBaseDirFile,
                         String expectedTryContent) throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      String originalRuntimeExceptions = null;
      try {
         // Store original settings of KeY which requires that at least one proof was instantiated.
         if (!SymbolicExecutionUtil.isChoiceSettingInitialised()) {
            createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, baseContractName, false, false, false);
         }
         originalRuntimeExceptions = SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);
         assertNotNull(originalRuntimeExceptions);
         SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW);
         // Create proof environment for symbolic execution
         SymbolicExecutionEnvironment<CustomConsoleUserInterface> env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, baseContractName, false, false, false);
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