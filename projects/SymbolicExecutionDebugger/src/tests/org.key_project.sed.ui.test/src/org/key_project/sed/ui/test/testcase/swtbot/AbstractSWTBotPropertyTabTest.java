package org.key_project.sed.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotPerspective;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.ui.test.util.SWTBotTabbedPropertyList;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides the basic functionality to test property tabs.
 * @author Martin Hentschel
 */
public class AbstractSWTBotPropertyTabTest extends TestCase {
   /**
    * Does some test steps on the fixed example model.
    * @param steps The test steps to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doFixedExampleTest(ITestSteps steps) throws Exception {
      // Test parameters
      assertNotNull(steps);
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotPerspective defaultPerspective = bot.activePerspective();
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
         SWTBotView propertiesView = TestSedCoreUtil.getPropertiesView(bot);
         // Select first thread
         selectThread(debugTree);
         SWTBotTabbedPropertyList tabs = SWTBotTabbedPropertyList.tabbedPropertyList(propertiesView.bot());
         assertNotNull(tabs);
         steps.assertThread(debugTree, propertiesView, tabs);
         // Select first statement
         selectStatement(debugTree);
         steps.assertStatement(debugTree, propertiesView, tabs);
         // Select debug target
         selectDebugTarget(debugTree);
         steps.assertDebugTarget(debugTree, propertiesView, tabs);
         // Select method return
         selectMethodReturn(debugTree);
         steps.assertMethodReturn(debugTree, propertiesView, tabs);
      }
      finally {
         defaultPerspective.activate();
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
   }

   /**
    * Selects an {@link ISEDMethodReturn}.
    * @param debugTree The {@link SWTBotTree} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectMethodReturn(SWTBotTree debugTree) {
      TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0, 5, 1, 1, 0, 0);
   }

   /**
    * Selects an {@link ISEDDebugTarget}.
    * @param debugTree The {@link SWTBotTree} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectDebugTarget(SWTBotTree debugTree) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0);
   }

   /**
    * Selects an {@link ISEDThread}.
    * @param debugTree The {@link SWTBotTree} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectThread(SWTBotTree debugTree) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0);
   }

   /**
    * Selects an {@link ISEDStatement}.
    * @param debugTree The {@link SWTBotTree} to select in.
    * @throws Exception Occurred Exception.
    */
   protected void selectStatement(SWTBotTree debugTree) throws Exception {
      TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0, 0);
   }

   /**
    * Defines the test steps to execute via {@link AbstractSWTBotPropertyTabTest#doFixedExampleTest(ITestSteps)}.
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
   }
}
