package org.key_project.sed.core.test.util;

import junit.framework.TestCase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.LaunchUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides static methods that makes testing easier
 * @author Martin Hentschel
 */
public final class TestSedCoreUtil {
   /**
    * The ID of the fixed example launch configuration type.
    */
   public static final String FIXED_EXAMPLE_LAUNCH_CONFIGURATION_TYPE_ID = "org.key_project.sed.core.test.example.fixed_launch_content";

   /**
    * The launch mode supported by the fixed example.
    */
   public static final String FIXED_EXAMPLE_MODE = "debug";
   
   /**
    * Forbid instances.
    */
   private TestSedCoreUtil() {
   }
   
   /**
    * Returns the {@link ILaunchConfigurationType} of the fixed example.
    * @return The {@link ILaunchConfigurationType} of the fixed example.
    */
   public static ILaunchConfigurationType getFixedExampleConfigurationType() {
       return LaunchUtil.getConfigurationType(FIXED_EXAMPLE_LAUNCH_CONFIGURATION_TYPE_ID);            
   }
   
   /**
    * Creates a new fixed example {@link ILaunchConfiguration}.
    * @return The created {@link ILaunchConfiguration}.
    * @throws CoreException Occurred Exception.
    */
   public static ILaunchConfiguration createFixedExampleLaunchConfiguration() throws CoreException {
      ILaunchConfiguration config = null;
      ILaunchConfigurationWorkingCopy wc = null;
      ILaunchConfigurationType configType = getFixedExampleConfigurationType();
      wc = configType.newInstance(null, LaunchUtil.getLaunchManager().generateLaunchConfigurationName("Fixed Example Test"));
      config = wc.doSave();
      return config;
   }
   
   /**
    * Launches the fixed example.
    * @throws CoreException Occurred Exception.
    */
   public static void launchFixedExample() throws CoreException {
      ILaunchConfiguration config = createFixedExampleLaunchConfiguration();
      DebugUITools.launch(config, FIXED_EXAMPLE_MODE);
   }

   /**
    * Opens the "Symbolic Debug" perspective.
    * @param bot The {@link SWTWorkbenchBot} to use.
    */
   public static void openSymbolicDebugPerspective(SWTWorkbenchBot bot) {
      // Open perspective selection dialog
      bot.menu("Window").menu("Open Perspective").menu("Other...").click();
      // Get dialog, select perspective and close it
      SWTBotShell shell = bot.shell("Open Perspective");
      SWTBotTable table = shell.bot().table();
      table.select("Symbolic Debug");
      shell.bot().button("OK").click();
      // Make sure that the perspective is opened
      TestCase.assertFalse(shell.isOpen());
      TestCase.assertTrue(bot.perspectiveByLabel("Symbolic Debug").isActive());
   }

   /**
    * Returns the {@link SWTBotView} for the debug view.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @return The {@link SWTBotView}.
    */
   public static SWTBotView getDebugView(SWTWorkbenchBot bot) {
      return bot.viewById(IDebugUIConstants.ID_DEBUG_VIEW);
   }

   /**
    * Makes sure that only the fixed example is shown in the given {@link SWTBotTree}.
    * @param debugTree The {@link SWTBotTree} to check.
    */
   public static void assertFixedExample(SWTBotTree debugTree) {
      // Assert launch
      SWTBotTreeItem[] launchItems = debugTree.getAllItems();
      TestCase.assertEquals(1, launchItems.length);
      TestCase.assertEquals("Fixed Example Test [Fixed Example]", launchItems[0].getText());
      // Assert target
      SWTBotTreeItem[] targetItems = launchItems[0].getItems();
      TestCase.assertEquals(1, targetItems.length);
      TestCase.assertEquals("Fixed Example Target", targetItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(targetItems[0]) instanceof ISEDDebugTarget);
      // Assert thread
      SWTBotTreeItem[] threadItems = targetItems[0].getItems();
      TestCase.assertEquals(1, threadItems.length);
      TestCase.assertEquals("Fixed Example Thread", threadItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(threadItems[0]) instanceof ISEDThread);
      // Assert statement1
      SWTBotTreeItem[] statement1Items = threadItems[0].getItems();
      TestCase.assertEquals(1, statement1Items.length);
      TestCase.assertEquals("int x = 1;", statement1Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statement1Items[0]) instanceof ISEDStatement);
      // Assert statement2
      SWTBotTreeItem[] statement2Items = statement1Items[0].getItems();
      TestCase.assertEquals(1, statement2Items.length);
      TestCase.assertEquals("int y = 2;", statement2Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statement2Items[0]) instanceof ISEDStatement);
      // Assert statement3
      SWTBotTreeItem[] statement3Items = statement2Items[0].getItems();
      TestCase.assertEquals(1, statement3Items.length);
      TestCase.assertEquals("int result = (x + y) / z;", statement3Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statement3Items[0]) instanceof ISEDStatement);
      // Assert branch conditions
      SWTBotTreeItem[] conditions1Items = statement3Items[0].getItems();
      TestCase.assertEquals(2, conditions1Items.length);
      TestCase.assertEquals("z == 0", conditions1Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions1Items[0]) instanceof ISEDBranchCondition);
      TestCase.assertEquals("z != 0", conditions1Items[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions1Items[1]) instanceof ISEDBranchCondition);
      // Assert branch zero
      SWTBotTreeItem[] branchZeroItems = conditions1Items[0].getItems();
      TestCase.assertEquals(1, branchZeroItems.length);
      TestCase.assertEquals("throws DivisionByZeroException()", branchZeroItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchZeroItems[0]) instanceof ISEDExceptionalTermination);
      // Assert branch not zero
      SWTBotTreeItem[] branchNotZeroItems = conditions1Items[1].getItems();
      TestCase.assertEquals(1, branchNotZeroItems.length);
      TestCase.assertEquals("foo(result)", branchNotZeroItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchNotZeroItems[0]) instanceof ISEDMethodCall);
      // Assert method call
      SWTBotTreeItem[] callItems = branchNotZeroItems[0].getItems();
      TestCase.assertEquals(1, callItems.length);
      TestCase.assertEquals("if (result >= 0)", callItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(callItems[0]) instanceof ISEDBranchNode);
      // Assert branch conditions
      SWTBotTreeItem[] conditions2Items = callItems[0].getItems();
      TestCase.assertEquals(2, conditions2Items.length);
      TestCase.assertEquals("result < 0", conditions2Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions2Items[0]) instanceof ISEDBranchCondition);
      TestCase.assertEquals("result >= 0", conditions2Items[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions2Items[1]) instanceof ISEDBranchCondition);
      // Assert branch negative
      SWTBotTreeItem[] negativeItems = conditions2Items[0].getItems();
      TestCase.assertEquals(1, negativeItems.length);
      TestCase.assertEquals("return -1", negativeItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(negativeItems[0]) instanceof ISEDMethodReturn);
      // Assert termination negative
      SWTBotTreeItem[] negativeTerminationItems = negativeItems[0].getItems();
      TestCase.assertEquals(1, negativeTerminationItems.length);
      TestCase.assertEquals("<end>", negativeTerminationItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(negativeTerminationItems[0]) instanceof ISEDTermination);
      // Assert termination negative empty
      SWTBotTreeItem[] negativeTerminationEmptyItems = negativeTerminationItems[0].getItems();
      TestCase.assertEquals(0, negativeTerminationEmptyItems.length);
      // Assert branch positive
      SWTBotTreeItem[] positiveItems = conditions2Items[1].getItems();
      TestCase.assertEquals(1, positiveItems.length);
      TestCase.assertEquals("return 1", positiveItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(positiveItems[0]) instanceof ISEDMethodReturn);
      // Assert termination positive
      SWTBotTreeItem[] positiveTerminationItems = positiveItems[0].getItems();
      TestCase.assertEquals(1, positiveTerminationItems.length);
      TestCase.assertEquals("<end>", positiveTerminationItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(positiveTerminationItems[0]) instanceof ISEDTermination);
      // Assert termination positive empty
      SWTBotTreeItem[] positiveTerminationEmptyItems = positiveTerminationItems[0].getItems();
      TestCase.assertEquals(0, positiveTerminationEmptyItems.length);
   }

   /**
    * Terminates and removes all {@link ILaunch}s in the given tree.
    * @param debugTree The given tree.
    */
   public static void terminateAndRemoveAll(SWTBotTree debugTree) {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Terminate all items
      SWTBotTreeItem[] launchItems = debugTree.getAllItems();
      for (SWTBotTreeItem item : launchItems) {
         item.select();
         item.contextMenu("Terminate and Remove").click();
         SWTBotShell dialog = bot.shell("Terminate and Remove");
         dialog.bot().button("Yes").click();
      }
      // Wait until all items are removed
      bot.waitWhile(Conditions.treeHasRows(debugTree, 1));
      // Make sure that the tree has no items
      launchItems = debugTree.getAllItems();
      TestCase.assertEquals(0, launchItems.length);
   }
}
