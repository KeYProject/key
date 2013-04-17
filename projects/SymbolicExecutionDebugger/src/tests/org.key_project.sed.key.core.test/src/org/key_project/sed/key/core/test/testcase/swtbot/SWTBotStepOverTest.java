/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IStep;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;

/**
 * Tests the step over functionality of an {@link IDebugTarget} and
 * each contained {@link IStep}.
 * @author Martin Hentschel
 */
public class SWTBotStepOverTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Tests the step over functionality on each branch separately.
    */
   @Test
   public void testStepOverOnOneBranchOnly() throws Exception {
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            // Get debug target TreeItem
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
            // Test initial debug target
            String expectedModelPathInBundle = "data/stepOverOnTwoBranches/oracleOnBranchOnly/StepOverOnTwoBranches";
            String expectedModelFileExtension = ".xml";
            int modelIndex = 0;
            assertStep(target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension);
            // Step into
            assertStepInto(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // main method
            assertStepInto(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // if
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // i = 2
            item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0, 1, 0, 0); // Select first i = 2 statement
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // j = 3 on first branch
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // x = valueLonger(i) on first branch
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // y = value(j) on first branch
            item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0, 1, 1, 0); // Select second i = 2 statement
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // j = 3 on second branch
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // x = valueLonger(i) on second branch
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // y = value(j) on second branch
            item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // z
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // zz
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // return statement
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // method return -2
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // end
         }
      };
      doKeYDebugTargetTest("SWTBotStepOverTest_testStepOverOnOneBranchOnly", 
                           "data/stepOverOnTwoBranches/test", 
                           true,
                           true,
                           createMethodSelector("StepOverOnTwoBranches", "main", "I"), 
                           null,
                           null,
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }

   /**
    * Tests the step over functionality on two branches.
    */
   @Test
   public void testStepOverOnTwoBranches() throws Exception {
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            // Get debug target TreeItem
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select first thread
            // Test initial debug target
            String expectedModelPathInBundle = "data/stepOverOnTwoBranches/oracleTwoBranches/StepOverOnTwoBranches";
            String expectedModelFileExtension = ".xml";
            int modelIndex = 0;
            assertStep(target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension);
            // Step into
            assertStepInto(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // main method
            assertStepInto(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // if
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // i = 2
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // j = 3
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // x = valueLonger(i)
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // y = value(j)
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // z
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // zz
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // return statement
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // method return -2
            assertStepOver(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // end
         }
      };
      doKeYDebugTargetTest("SWTBotStepOverTest_testStepOverOnTwoBranches", 
                           "data/stepOverOnTwoBranches/test", 
                           true,
                           true,
                           createMethodSelector("StepOverOnTwoBranches", "main", "I"), 
                           null,
                           null,
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           4, 
                           executor);
   }
}