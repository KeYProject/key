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

import org.eclipse.core.resources.ResourcesPlugin;
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
import org.key_project.sed.key.core.test.util.TestBreakpointsUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotChangeCaughtUncaughtSubclasses extends AbstractKeYDebugTargetTestCase {
   
   private static final String CALLER_PATH= ResourcesPlugin.getWorkspace().getRoot().getRawLocation().toString() + "/SWTBotChangeCaughtUncaughtSubclasses_test/src/BreakpointStopCallerAndLoop.java";
   
   @Test
   public void test() throws Exception{
      IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {            
            // Get debug target TreeItem
            TestBreakpointsUtil.addSomeBreakpoints(CALLER_PATH, bot, "NullpointerException", "ClassCastException", "java.lang.Exception");
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0);
            resume(bot, item, target);
            assertTrue(TestBreakpointsUtil.checkTargetCaughtUncaughtSubclass(target, 3,3,0));
            assertTrue(TestBreakpointsUtil.checkProofCaughtUncaughtSubclass(target,  3,3,0));
            assertTrue(TestBreakpointsUtil.changeCaughtUncaughtSubclass(bot, "NullPointerException: caught and uncaught", false, true, false));
            assertTrue(TestBreakpointsUtil.changeCaughtUncaughtSubclass(bot, "ClassCastException: caught and uncaught", true, false, false));
            assertTrue(TestBreakpointsUtil.changeCaughtUncaughtSubclass(bot, "Exception: caught and uncaught", true, true, true));
            TestUtilsUtil.sleep(2000);
            assertTrue(TestBreakpointsUtil.checkTargetCaughtUncaughtSubclass(target, 2,2,1));
            assertTrue(TestBreakpointsUtil.checkProofCaughtUncaughtSubclass(target,  2,2,1));
            TestBreakpointsUtil.removeAllBreakpoints();
         }
      };
      doKeYDebugTargetTest("SWTBotChangeCaughtUncaughtSubclasses_test",
            "data/BreakpointTest/test",
            true,
            true,
            createMethodSelector("BreakpointStopCallerAndLoop", "main"),
            null,
            null,
            Boolean.FALSE,
            Boolean.FALSE,
            Boolean.FALSE,
            Boolean.FALSE,
            Boolean.FALSE,
            Boolean.FALSE,
            Boolean.TRUE,
            8, executor);   
   } 
}