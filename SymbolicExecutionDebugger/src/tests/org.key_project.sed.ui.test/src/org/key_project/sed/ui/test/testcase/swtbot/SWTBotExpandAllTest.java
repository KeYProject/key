package org.key_project.sed.ui.test.testcase.swtbot;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.ui.command.ExpandAllCommand;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests {@link ExpandAllCommand} and 
 * {@link SEDUIUtil#expandInDebugView(org.eclipse.ui.IWorkbenchPart, org.key_project.sed.ui.util.IDebugView, java.util.List)}
 * @author Martin Hentschel
 */
public class SWTBotExpandAllTest extends AbstractSetupTestCase {
   /**
    * Tests expand all in the fixed example.
    */
   @Test
   public void testExpandAll() throws Exception {
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
         // Select debug target to expand
         SWTBotTreeItem targetItem = TestUtilsUtil.selectInTree(debugTree, 0, 0);
         targetItem.collapse();
         // Expand all
         TestUtilsUtil.clickContextMenu(debugTree, "Expand All");
         TestUtilsUtil.waitUntilExpanded(bot, targetItem);
         targetItem = TestUtilsUtil.selectInTree(debugTree, 0, 0);
         assertExpanded(targetItem);
      }
      finally {
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }

   /**
    * Ensures that the subtree starting at the item is expanded.
    * @param item The item to test.
    */
   protected void assertExpanded(SWTBotTreeItem item) {
      SWTBotTreeItem[] children = item.getItems();
      if (!ArrayUtil.isEmpty(children)) {
         assertTrue(item.isExpanded());
      }
      for (SWTBotTreeItem child : children) {
         assertExpanded(child);
      }
   }
}
