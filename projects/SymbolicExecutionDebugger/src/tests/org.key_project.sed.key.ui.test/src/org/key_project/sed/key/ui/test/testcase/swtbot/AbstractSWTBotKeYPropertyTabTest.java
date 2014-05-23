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

package org.key_project.sed.key.ui.test.testcase.swtbot;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.test.testcase.swtbot.AbstractKeYDebugTargetTestCase;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides the basic functionality to test KeY specific property tabs.
 * @author Martin Hentschel
 */
public class AbstractSWTBotKeYPropertyTabTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Does some test steps on the flat steps example.
    * @param projectName The project name to extract test data into.
    * @param steps The test steps to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doFlatStepsTest(String projectName, final ITestSteps steps) throws Exception {
      IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            // Resume on thread
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0); // Select thread
            resume(bot, item, target);
            // Get properties view
            SWTBotView propertiesView = TestUtilsUtil.getPropertiesView(bot);
            // Select first thread
            selectThread(debugView);
            SWTBotTabbedPropertyList tabs = SWTBotTabbedPropertyList.tabbedPropertyList(propertiesView.bot());
            assertNotNull(tabs);
            steps.assertThread(debugTree, propertiesView, tabs);
            // Select first statement
            selectStatement(debugView);
            steps.assertStatement(debugTree, propertiesView, tabs);
            // Select debug target
            selectDebugTarget(debugView);
            steps.assertDebugTarget(debugTree, propertiesView, tabs);
            // Select method return
            selectMethodReturn(debugView);
            steps.assertMethodReturn(debugTree, propertiesView, tabs);
            // Select launch
            selectLaunch(debugView);
            steps.assertLaunch(debugTree, propertiesView, tabs);
         }
      };
      doKeYDebugTargetTest(projectName, 
                           Activator.PLUGIN_ID,
                           "data/statements", 
                           false,
                           false, 
                           createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"), 
                           null,
                           null,
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE,
                           8, 
                           executor);
   }

   /**
    * Selects an {@link ISEDMethodReturn}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectLaunch(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0);
   }

   /**
    * Selects an {@link ISEDMethodReturn}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectMethodReturn(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0, 4);
   }

   /**
    * Selects an {@link ISEDDebugTarget}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectDebugTarget(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0);
   }

   /**
    * Selects an {@link ISEDThread}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectThread(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0);
   }

   /**
    * Selects an {@link ISEDStatement}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectStatement(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0, 1);
   }

   /**
    * Defines the test steps to execute via {@link AbstractSWTBotKeYPropertyTabTest#doFlatStepsTest(ITestSteps)}.
    * @author Martin Hentschel
    */
   protected static interface ITestSteps {
      /**
       * Do some assertions on an {@link ISEDThread}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertThread(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ISEDStatement}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertStatement(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ISEDDebugTarget}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertDebugTarget(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ISEDMethodReturn}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertMethodReturn(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ILaunch}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertLaunch(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;
   }
}