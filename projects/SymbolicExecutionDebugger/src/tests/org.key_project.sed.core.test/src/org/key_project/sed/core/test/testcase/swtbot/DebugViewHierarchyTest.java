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
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Makes sure that the hierarchy of symbolic execution trees is correctly
 * shown in the debug view of the Eclipse debug API.
 * @author Martin Hentschel
 */
public class DebugViewHierarchyTest extends TestCase {
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
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective(bot);
         // Launch fixed example
         TestSedCoreUtil.launchFixedExample();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         SWTBotTree debugTree = debugView.bot().tree();
         bot.waitUntil(Conditions.treeHasRows(debugTree, 1));
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertFixedExample(debugTree);
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
      finally {
         defaultPerspective.activate();
      }
   }
}
