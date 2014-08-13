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
import org.key_project.sed.key.core.test.Activator;

/**
 * Tests the step return functionality of an {@link IDebugTarget} and
 * each contained {@link IStep}.
 * @author Martin Hentschel
 */
public class SWTBotStepReturnTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Tests the step over functionality on two branches.
    */
   @Test
   public void testStepReturn() throws Exception {
      IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            // Get debug target TreeItem
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select first thread
            // Test initial debug target
            String expectedModelPathInBundle = "data/stepReturnTest/oracle/StepReturnTest";
            String expectedModelFileExtension = ".xml";
            int modelIndex = 0;
            assertStep(target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension);
            // Step into
            assertStepInto(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // call main
            assertStepInto(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // first level
            assertStepInto(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // call first level
            assertStepInto(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // second level
            assertStepInto(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // call second level
            assertStepInto(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // third level
            assertStepInto(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // call third level
            assertStepInto(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // fourth level
            assertStepInto(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // call fourth level
            assertStepReturn(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // a = a * 2
            assertStepReturn(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // second level
            assertStepReturn(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // first level
            assertStepReturn(bot, item, target, Activator.PLUGIN_ID, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension); // end
         }
      };
      doKeYDebugTargetTest("SWTBotStepReturnTest_testStepReturn", 
                           "data/stepReturnTest/test", 
                           true,
                           true,
                           createMethodSelector("StepReturnTest", "main", "I"), 
                           null,
                           null,
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE, 
                           4, executor);
   }
}