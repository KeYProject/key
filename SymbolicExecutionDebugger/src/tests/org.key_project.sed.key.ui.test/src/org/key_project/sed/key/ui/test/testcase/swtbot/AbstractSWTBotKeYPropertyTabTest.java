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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISELoopBodyTermination;
import org.key_project.sed.core.model.ISELoopInvariant;
import org.key_project.sed.core.model.ISEMethodContract;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISEStatement;
import org.key_project.sed.core.model.ISETermination;
import org.key_project.sed.core.model.ISEThread;
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
    * Does some test steps on the all node types example.
    * @param projectName The project name to extract test data into.
    * @param steps The test steps to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doAllNodeTypesTest(String projectName, final ITestSteps steps) throws Exception {
      IKeYDebugTargetProofFileTestExecutor executor = new IKeYDebugTargetProofFileTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IFile file, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0); // Select thread
            resume(bot, item, target);
            // Wait until jobs are done
            TestUtilsUtil.sleep(2000); // Give the UI the chance to start jobs
            TestUtilsUtil.waitForJobs(); // Wait until selection is synchronized
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
            // Select method contract
            selectMethodContract(debugView);
            steps.assertMethodContract(debugTree, propertiesView, tabs);
            // Select loop invariant
            selectLoopInvariant(debugView);
            steps.assertLoopInvariant(debugTree, propertiesView, tabs);
            // Select loop body termination
            selectLoopBodyTermination(debugView);
            steps.assertLoopBodyTermination(debugTree, propertiesView, tabs);
            // Select termination
            selectTermination(debugView);
            steps.assertTermination(debugTree, propertiesView, tabs);
            // Select launch
            selectLaunch(debugView);
            steps.assertLaunch(debugTree, propertiesView, tabs);
         }
      };
      doKeYDebugTargetTest(projectName, 
                           Activator.PLUGIN_ID, 
                           "data/allNodeTypesTest/test", 
                           false, 
                           false, 
                           new IFileSelector() {
                              @Override
                              public IFile getFile(IJavaProject project) throws Exception {
                                 return project.getProject().getFile(new Path("src/AllNodeTypesTest.proof"));
                              }
                           }, 
                           false, 
                           false, 
                           false, 
                           false, 
                           false, 
                           true,
                           true,
                           8, 
                           executor);
   }

   /**
    * Selects an {@link ISEMethodReturn}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectLaunch(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0);
   }

   /**
    * Selects an {@link ISEMethodReturn}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectMethodReturn(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0, 1, 0, 4, 1, 11);
   }

   /**
    * Selects an {@link ISEMethodContract}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectMethodContract(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0, 1, 0, 0);
   }

   /**
    * Selects an {@link ISEDebugTarget}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectDebugTarget(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0);
   }

   /**
    * Selects an {@link ISEThread}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectThread(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0);
   }

   /**
    * Selects an {@link ISEStatement}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectStatement(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0, 1);
   }

   /**
    * Selects an {@link ISELoopInvariant}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectLoopInvariant(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0, 1, 0, 4);
   }

   /**
    * Selects an {@link ISELoopBodyTermination}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectLoopBodyTermination(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0, 1, 0, 4, 0, 3);
   }

   /**
    * Selects an {@link ISETermination}.
    * @param debugView The {@link SWTBotView} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectTermination(SWTBotView debugView) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0, 1, 0, 4, 1, 12);
   }

   /**
    * Defines the test steps to execute via {@link AbstractSWTBotKeYPropertyTabTest#doFlatStepsTest(ITestSteps)}.
    * @author Martin Hentschel
    */
   protected static interface ITestSteps {
      /**
       * Do some assertions on an {@link ISEThread}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertThread(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ISEStatement}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertStatement(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ISEDebugTarget}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertDebugTarget(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ISEMethodReturn}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertMethodReturn(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ISEMethodContract}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertMethodContract(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ISETermination}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertTermination(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ISELoopInvariant}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertLoopInvariant(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

      /**
       * Do some assertions on an {@link ISELoopBodyTermination}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertLoopBodyTermination(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs) throws Exception;

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