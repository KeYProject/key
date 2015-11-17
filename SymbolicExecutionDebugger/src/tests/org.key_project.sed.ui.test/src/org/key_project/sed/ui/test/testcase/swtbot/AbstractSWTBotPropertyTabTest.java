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

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISEStatement;
import org.key_project.sed.core.model.ISEThread;
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
         selectDebugTarget(debugView);
         selectThread(debugView);
         selectStatement(debugView);
         selectMethodReturn(debugView);
         Thread.sleep(1000); // Some extra time for the Debug API to set the selection
         // Select and test debug target in once because otherwise the selection can be changed by Eclipse itself.
         ISEDebugTarget target = selectDebugTarget(debugView);
         steps.assertDebugTarget(debugTree, propertiesView, getPropertiesTabs(propertiesView), target);
         // Select first thread
         ISEThread thread = selectThread(debugView);
         steps.assertThread(debugTree, propertiesView, getPropertiesTabs(propertiesView), thread);
         // Select first statement
         ISEStatement statement = selectStatement(debugView);
         steps.assertStatement(debugTree, propertiesView, getPropertiesTabs(propertiesView), statement);
         // Select debug target
         target = selectDebugTarget(debugView);
         steps.assertDebugTarget(debugTree, propertiesView, getPropertiesTabs(propertiesView), target);
         // Select method return
         ISEMethodReturn methodReturn = selectMethodReturn(debugView);
         steps.assertMethodReturn(debugTree, propertiesView, getPropertiesTabs(propertiesView), methodReturn);
         // Select method call
         ISEMethodCall methodCall = selectMethodCall(debugView);
         steps.assertMethodCall(debugTree, propertiesView, getPropertiesTabs(propertiesView), methodCall);
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
    * Selects an {@link ISEMethodReturn}.
    * @param debugView The {@link SWTBotView} to select in.
    * @return The selected {@link ISEMethodReturn}.
    * @throws Exception Occurred Exception.
    */
   protected ISEMethodReturn selectMethodReturn(SWTBotView debugView) throws Exception {
      Object data = selectInDebugTree(debugView, 0, 0, 0, 5, 1, 1, 0, 0);
      assertTrue(data instanceof ISEMethodReturn);
      return (ISEMethodReturn)data;
   }

   /**
    * Selects an {@link ISEDebugTarget}.
    * @param debugView The {@link SWTBotView} to select in.
    * @return The selected {@link ISEDebugTarget}.
    * @throws Exception Occurred Exception.
    */
   protected ISEDebugTarget selectDebugTarget(SWTBotView debugView) throws Exception {
      Object data = selectInDebugTree(debugView, 0, 0);
      assertTrue(data instanceof ISEDebugTarget);
      return (ISEDebugTarget)data;
   }

   /**
    * Selects an {@link ISEThread}.
    * @param debugView The {@link SWTBotView} to select in.
    * @return The selected {@link ISEThread}.
    * @throws Exception Occurred Exception.
    */
   protected ISEThread selectThread(SWTBotView debugView) throws Exception {
      Object data = selectInDebugTree(debugView, 0, 0, 0);
      assertTrue(data instanceof ISEThread);
      return (ISEThread)data;
   }

   /**
    * Selects an {@link ISEStatement}.
    * @param debugView The {@link SWTBotView} to select in.
    * @return The selected {@link ISEStatement}.
    * @throws Exception Occurred Exception.
    */
   protected ISEStatement selectStatement(SWTBotView debugView) throws Exception {
      Object data = selectInDebugTree(debugView, 0, 0, 0, 0);
      assertTrue(data instanceof ISEStatement);
      return (ISEStatement)data;
   }

   /**
    * Selects an {@link ISEMethodCall}.
    * @param debugTree The {@link SWTBotView} to select in.
    * @return The selected {@link ISEMethodCall}.
    * @throws Exception Occurred Exception.
    */
   protected ISEMethodCall selectMethodCall(SWTBotView debugView) throws Exception {
      Object data = selectInDebugTree(debugView, 0, 0, 0, 5, 1, 0);
      assertTrue(data instanceof ISEMethodCall);
      return (ISEMethodCall)data;
   }
   
   /**
    * Selects the element at the given index. 
    * @param debugView The {@link SWTBotView} to select in.
    * @param indexPathToItem The path to the item to select.
    * @return The selected object.
    * @throws DebugException Occurred Exception
    */
   protected Object selectInDebugTree(SWTBotView debugView, int... indexPathToItem) throws DebugException {
      SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugView, indexPathToItem);
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
       * Do some assertions on an {@link ISEThread}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertThread(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEThread thread) throws Exception;

      /**
       * Do some assertions on an {@link ISEStatement}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertStatement(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEStatement statement) throws Exception;

      /**
       * Do some assertions on an {@link ISEDebugTarget}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertDebugTarget(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDebugTarget target) throws Exception;

      /**
       * Do some assertions on an {@link ISEMethodReturn}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertMethodReturn(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEMethodReturn methodReturn) throws Exception;

      /**
       * Do some assertions on an {@link ISEMethodCall}.
       * @param debugTree The debug tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertMethodCall(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEMethodCall methodCall) throws Exception;
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