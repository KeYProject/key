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

import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.test.Activator;

/**
 * Tests the defined contract in a launch configuration which
 * includes existing contracts or defined preconditions.
 * @author Martin Hentschel
 */
public class SWTBotContractTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Launches a method and uses an existing operation contract with ID 1.
    */
   @Test
   public void testGeneratedContract_Contract1() throws Exception {
      doContractTest("SWTBotContractTest_testGeneratedContract_Contract1", 
                     true, 
                     "ContractTest[ContractTest::returnValue(int)].JML operation contract.1", 
                     "data/contractTest/oracle/ContractTest_Contract1.xml");
   }

   /**
    * Launches a method and uses an existing operation contract with ID 0.
    */
   @Test
   public void testGeneratedContract_Contract0() throws Exception {
      doContractTest("SWTBotContractTest_testGeneratedContract_Contract0", 
                     true, 
                     "ContractTest[ContractTest::returnValue(int)].JML operation contract.0", 
                     "data/contractTest/oracle/ContractTest_Contract0.xml");
   }

   /**
    * Launches a method with generated contract which has a precondition.
    */
   @Test
   public void testGeneratedContract_Precondition() throws Exception {
      doContractTest("SWTBotContractTest_testGeneratedContract_Precondition", 
                     false, 
                     "value == 42", 
                     "data/contractTest/oracle/ContractTest_Precondition42.xml");
   }

   /**
    * Launches a method with generated contract which has no precondition.
    */
   @Test
   public void testGeneratedContract_NoPrecondition() throws Exception {
      doContractTest("SWTBotContractTest_testGeneratedContract_NoPrecondition", 
                     false, 
                     null, 
                     "data/contractTest/oracle/ContractTest.xml");
   }
   
   /**
    * Does the test steps of
    * {@link #testGeneratedContract_Contract0()},
    * {@link #testGeneratedContract_Contract1()},
    * {@link #testGeneratedContract_NoPrecondition()} and
    * {@link #testGeneratedContract_Precondition()}.
    * @param projectName The project name to use.
    * @param useExistingContract Use an existing contract?
    * @param preconditionOrExistingContractId Precondition or ID of contract to use.
    * @param expectedModelPathInBundle Expected path in plug-in to oracle file.
    * @throws Exception Occurred Exception.
    */
   protected void doContractTest(String projectName,
                                 boolean useExistingContract,
                                 String preconditionOrExistingContractId,
                                 final String expectedModelPathInBundle) throws Exception {
      IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            // Get debug target TreeItem
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
            // Do resume and test created tree
            resume(bot, item, target);
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, expectedModelPathInBundle, false, false);
         }
      };
      doKeYDebugTargetTest(projectName, 
                           "data/contractTest/test", 
                           true,
                           true,
                           createMethodSelector("ContractTest", "returnValue", "I"), 
                           Boolean.valueOf(useExistingContract),
                           preconditionOrExistingContractId,
                           Boolean.TRUE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           8, 
                           executor);
   }
}