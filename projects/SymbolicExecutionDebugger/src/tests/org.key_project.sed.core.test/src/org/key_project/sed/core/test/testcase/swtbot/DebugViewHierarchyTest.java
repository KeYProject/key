package org.key_project.sed.core.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotPerspective;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Makes sure that the hierarchy of symbolic execution trees is correctly
 * shown in the debug view of the Eclipse debug API.
 * @author Martin Hentschel
 */
public class DebugViewHierarchyTest extends TestCase {
   /**
    * Makes sure that the tree is updated when the user switches between
    * normal and compact view.
    */
   @Test
   public void testSwitchingBetweenCompactAndNormalHierarchy() throws CoreException {
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      // Disable compact view
      boolean originalCompactView = SEDPreferenceUtil.isShowCompactExecutionTree();
      SEDPreferenceUtil.setShowCompactExecutionTree(true);
      SWTBotTree debugTree = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective(bot);
         // Launch fixed example
         TestSedCoreUtil.launchFixedExample();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         bot.waitUntil(Conditions.treeHasRows(debugTree, 1));
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         TestUtilsUtil.sleep(TestSedCoreUtil.USER_INTERFACE_DEBUG_TREE_WAIT_TIME); // Give the user interface the chance to update the tree
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertCompactFixedExample(debugTree);
         // Change to normal view
         SEDPreferenceUtil.toggleShowCompactExecutionTreePreference();
         TestUtilsUtil.sleep(TestSedCoreUtil.USER_INTERFACE_DEBUG_TREE_WAIT_TIME); // Give the user interface the chance to update the tree
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         TestUtilsUtil.sleep(TestSedCoreUtil.USER_INTERFACE_DEBUG_TREE_WAIT_TIME); // Give the user interface the chance to update the tree
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertFixedExample(debugTree);
         // Change to compact view
         SEDPreferenceUtil.toggleShowCompactExecutionTreePreference();
         TestUtilsUtil.sleep(TestSedCoreUtil.USER_INTERFACE_DEBUG_TREE_WAIT_TIME); // Give the user interface the chance to update the tree
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         TestUtilsUtil.sleep(TestSedCoreUtil.USER_INTERFACE_DEBUG_TREE_WAIT_TIME); // Give the user interface the chance to update the tree
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertCompactFixedExample(debugTree);
      }
      finally {
         defaultPerspective.activate();
         SEDPreferenceUtil.setShowCompactExecutionTree(originalCompactView);
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
   }
   
   /**
    * Makes sure that the defined hierarchy by the interface
    * {@link ISEDDebugElement} and his sub interfaces is correctly shown
    * in the debug view of the Eclipse debug API with activated
    * compact symbolic execution tree option.
    */
   @Test
   public void testCompactHierarchy() throws CoreException {
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      // Disable compact view
      boolean originalCompactView = SEDPreferenceUtil.isShowCompactExecutionTree();
      SEDPreferenceUtil.setShowCompactExecutionTree(true);
      SWTBotTree debugTree = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective(bot);
         // Launch fixed example
         TestSedCoreUtil.launchFixedExample();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         bot.waitUntil(Conditions.treeHasRows(debugTree, 1));
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         TestUtilsUtil.sleep(TestSedCoreUtil.USER_INTERFACE_DEBUG_TREE_WAIT_TIME); // Give the user interface the chance to update the tree
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertCompactFixedExample(debugTree);
      }
      finally {
         defaultPerspective.activate();
         SEDPreferenceUtil.setShowCompactExecutionTree(originalCompactView);
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
   }
   
   /**
    * Makes sure that the defined hierarchy by the interface
    * {@link ISEDDebugElement} and his sub interfaces is correctly shown
    * in the debug view of the Eclipse debug API.
    */
   @Test
   public void testHierarchy() throws CoreException {
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      // Disable compact view
      boolean originalCompactView = SEDPreferenceUtil.isShowCompactExecutionTree();
      SEDPreferenceUtil.setShowCompactExecutionTree(false);
      SWTBotTree debugTree = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective(bot);
         // Launch fixed example
         TestSedCoreUtil.launchFixedExample();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         bot.waitUntil(Conditions.treeHasRows(debugTree, 1));
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         TestUtilsUtil.sleep(TestSedCoreUtil.USER_INTERFACE_DEBUG_TREE_WAIT_TIME); // Give the user interface the chance to update the tree
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertFixedExample(debugTree);
      }
      finally {
         defaultPerspective.activate();
         SEDPreferenceUtil.setShowCompactExecutionTree(originalCompactView);
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
   }
}
