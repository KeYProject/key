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
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides the basic functionality to test property tabs.
 * @author Martin Hentschel
 */
public class AbstractSWTBotVariablesPropertyTabTest extends AbstractSetupTestCase {
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
         selectStatement(debugTree);
         Thread.sleep(1000); // Some extra time for the Debug API to set the selection
         TestUtilsUtil.waitForJobs();
         // Get variables view
         selectStatement(debugTree); // Because selection might have changed in between
         SWTBotView variablesView = TestSedCoreUtil.getVariablesView(bot);
         variablesView.show();
         SWTBotTree variablesTree = variablesView.bot().tree();
         variablesView.bot().waitUntil(Conditions.treeHasRows(variablesTree, 2));
         // Select and test first variable
         IVariable firstVariable = selectFirstVariable(variablesTree);
         steps.assertFirstVariable(variablesTree, propertiesView, getPropertiesTabs(propertiesView), firstVariable);
         // Select and test second variable
         IVariable secondVariable = selectSecondVariable(variablesTree);
         steps.assertSecondVariable(variablesTree, propertiesView, getPropertiesTabs(propertiesView), secondVariable);
         // Select and test first variable again
         IVariable firstVariableAgain = selectFirstVariable(variablesTree);
         steps.assertFirstVariable(variablesTree, propertiesView, getPropertiesTabs(propertiesView), firstVariableAgain);
         // Deselect variable
         variablesTree.select(new int[] {});
         steps.assertNoVariable(variablesTree, propertiesView, getPropertiesTabs(propertiesView));
         // Select and test second variable again
         IVariable secondVariableAgain = selectSecondVariable(variablesTree);
         steps.assertSecondVariable(variablesTree, propertiesView, getPropertiesTabs(propertiesView), secondVariableAgain);
         
      }
      finally {
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }

   /**
    * Selects the first {@link IVariable}.
    * @param variablesTree The {@link SWTBotTree} to select in.
    * @return The selected {@link IVariable}.
    * @throws Exception Occurred Exception.
    */
   protected IVariable selectFirstVariable(SWTBotTree variablesTree) throws Exception {
      Object data = selectInDebugTree(variablesTree, 0);
      assertTrue(data instanceof IVariable);
      return (IVariable)data;
   }

   /**
    * Selects the second {@link IVariable}.
    * @param variablesTree The {@link SWTBotTree} to select in.
    * @return The selected {@link IVariable}.
    * @throws Exception Occurred Exception.
    */
   protected IVariable selectSecondVariable(SWTBotTree variablesTree) throws Exception {
      Object data = selectInDebugTree(variablesTree, 1);
      assertTrue(data instanceof IVariable);
      return (IVariable)data;
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
    * Defines the test steps to execute via {@link AbstractSWTBotVariablesPropertyTabTest#doFixedExampleTest(ITestSteps)}.
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
       * Do some assertions on an {@link IVariable}.
       * @param variablesTree The variables tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @param variable The current {@link IVariable} to test.
       * @throws Exception Occurred Exception
       */
      public void assertFirstVariable(SWTBotTree variablesTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, IVariable variable);

      /**
       * Do some assertions on an {@link IVariable}.
       * @param variablesTree The variables tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @param variable The current {@link IVariable} to test.
       * @throws Exception Occurred Exception
       */
      public void assertSecondVariable(SWTBotTree variablesTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, IVariable variable);

      /**
       * Do some assertions if no {@link IVariable} is selected.
       * @param variablesTree The variables tree.
       * @param propertiesView The properties view.
       * @param tabs The properties view tabs.
       * @throws Exception Occurred Exception
       */
      public void assertNoVariable(SWTBotTree variablesTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs);
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