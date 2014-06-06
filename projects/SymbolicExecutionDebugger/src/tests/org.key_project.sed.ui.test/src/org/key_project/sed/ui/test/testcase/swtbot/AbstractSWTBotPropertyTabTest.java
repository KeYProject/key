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

package org.key_project.sed.ui.test.testcase.swtbot;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides the basic functionality to test property tabs.
 * @author Martin Hentschel
 */
public class AbstractSWTBotPropertyTabTest extends AbstractSetupTestCase {
   /**
    * Does some test steps on the fixed example model.
    * @param steps The test steps to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doFixedExampleTest(final ITestSteps steps) throws Exception {
      // Test parameters
      assertNotNull(steps);
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      SWTBotTree debugTree = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
         // Launch fixed example
         TestSedCoreUtil.launchFixedExample();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         // Get properties view
         SWTBotView propertiesView = TestUtilsUtil.getPropertiesView(bot);
         steps.initializeLaunch(TestSedCoreUtil.getFirstLaunch(debugTree));
         // Make sure that all nodes to test are loaded and that the automatic selection set to the debug target by the Debug API is done.
         selectDebugTarget(debugTree);
         selectThread(debugTree);
         selectStatement(debugTree);
         selectMethodReturn(debugTree);
         Thread.sleep(1000); // Some extra time for the Debug API to set the selection
         // Select and test debug target in once because otherwise the selection can be changed by Eclipse itself.
         ISEDDebugTarget target = selectDebugTarget(debugTree);
         steps.assertDebugTarget(debugTree, propertiesView, getPropertiesTabs(propertiesView), target);
         // Select first thread
         ISEDThread thread = selectThread(debugTree);
         steps.assertThread(debugTree, propertiesView, getPropertiesTabs(propertiesView), thread);
         // Select first statement
         ISEDStatement statement = selectStatement(debugTree);
         steps.assertStatement(debugTree, propertiesView, getPropertiesTabs(propertiesView), statement);
         // Select debug target
         target = selectDebugTarget(debugTree);
         steps.assertDebugTarget(debugTree, propertiesView, getPropertiesTabs(propertiesView), target);
         // Select method return
         ISEDMethodReturn methodReturn = selectMethodReturn(debugTree);
         steps.assertMethodReturn(debugTree, propertiesView, getPropertiesTabs(propertiesView), methodReturn);
      }
      finally {
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }

   /**
    * Returns the shown {@link SWTBotTabbedPropertyList}.
    * @param propertiesView The {@link SWTBotView} to search in.
    * @return The shown {@link SWTBotTabbedPropertyList}.
    */
   protected SWTBotTabbedPropertyList getPropertiesTabs(SWTBotView propertiesView) {
      SWTBotTabbedPropertyList tabs = SWTBotTabbedPropertyList.tabbedPropertyList(propertiesView.bot());
      assertNotNull(tabs);
      return tabs;
   }

   /**
    * Selects an {@link ISEDMethodReturn}.
    * @param debugTree The {@link SWTBotTree} to select in.
    * @return The selected {@link ISEDMethodReturn}.
    * @throws Exception Occurred Exception.
    */
   protected ISEDMethodReturn selectMethodReturn(SWTBotTree debugTree) {
      Object data = selectInDebugTree(debugTree, 0, 0, 0, 5, 1, 1, 0, 0);
      assertTrue(data instanceof ISEDMethodReturn);
      return (ISEDMethodReturn)data;
   }

   /**
    * Selects an {@link ISEDDebugTarget}.
    * @param debugTree The {@link SWTBotTree} to select in.
    * @return The selected {@link ISEDDebugTarget}.
    * @throws Exception Occurred Exception.
    */
   protected ISEDDebugTarget selectDebugTarget(SWTBotTree debugTree) throws Exception {
      Object data = selectInDebugTree(debugTree, 0, 0);
      assertTrue(data instanceof ISEDDebugTarget);
      return (ISEDDebugTarget)data;
   }

   /**
    * Selects an {@link ISEDThread}.
    * @param debugTree The {@link SWTBotTree} to select in.
    * @return The selected {@link ISEDThread}.
    * @throws Exception Occurred Exception.
    */
   protected ISEDThread selectThread(SWTBotTree debugTree) throws Exception {
      Object data = selectInDebugTree(debugTree, 0, 0, 0);
      assertTrue(data instanceof ISEDThread);
      return (ISEDThread)data;
   }

   /**
    * Selects an {@link ISEDStatement}.
    * @param debugTree The {@link SWTBotTree} to select in.
    * @return The selected {@link ISEDStatement}.
    * @throws Exception Occurred Exception.
    */
   protected ISEDStatement selectStatement(SWTBotTree debugTree) throws Exception {
      Object data = selectInDebugTree(debugTree, 0, 0, 0, 0);
      assertTrue(data instanceof ISEDStatement);
      return (ISEDStatement)data;
   }
   
   /**
    * Selects the element at the given index. 
    * @param debugTree The {@link SWTBotTree} to select in.
    * @param indexPathToItem The path to the item to select.
    * @return The selected object.
    */
   protected Object selectInDebugTree(SWTBotTree debugTree, int... indexPathToItem) {
      SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, indexPathToItem);
      return TestUtilsUtil.getTreeItemData(item);
   }

   /**
    * Defines the test steps to execute via {@link AbstractSWTBotPropertyTabTest#doFixedExampleTest(ITestSteps)}.
    * @author Martin Hentschel
    */
   protected static interface ITestSteps {
      /**
       * Initializes the given {@link ILaunch}.
       * @param firstLaunch The {@link ILaunch} to initialize.
       * @throws Exception Occurred Exception
       */
      public void initializeLaunch(ILaunch launch) throws Exception;

      /**
       * Do some assertions on an {@link ISEDThread}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertThread(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDThread thread) throws Exception;

      /**
       * Do some assertions on an {@link ISEDStatement}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertStatement(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDStatement statement) throws Exception;

      /**
       * Do some assertions on an {@link ISEDDebugTarget}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertDebugTarget(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDDebugTarget target) throws Exception;

      /**
       * Do some assertions on an {@link ISEDMethodReturn}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertMethodReturn(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDMethodReturn methodReturn) throws Exception;
   }
   
   /**
    * Provides some basic implementations of {@link ITestSteps}.
    * @author Martin Hentschel
    */
   protected static abstract class AbstractTestSteps implements ITestSteps {
      /**
       * {@inheritDoc}
       */
      @Override
      public void initializeLaunch(ILaunch launch) throws Exception {
      }
   }
}