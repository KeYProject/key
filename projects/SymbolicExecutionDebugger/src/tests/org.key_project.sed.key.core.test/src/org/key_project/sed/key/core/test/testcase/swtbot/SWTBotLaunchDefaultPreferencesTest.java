package org.key_project.sed.key.core.test.testcase.swtbot;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.key.core.util.KeYSEDPreferences;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests the launch configuration default values.
 * @author Martin Hentschel
 */
public class SWTBotLaunchDefaultPreferencesTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Tests the launch where return values are shown in tree.
    */
   @Test
   public void testShowMethodReturnValuesInDebugNodes() throws Exception {
      doTestShowMethodReturnValuesInDebugNodes("SWTBotLaunchDefaultPreferencesTest_testShowMethodReturnValuesInDebugNodes", true);
   }

   /**
    * Tests the launch where return values are not shown in tree.
    */
   @Test
   public void testDoNotShowMethodReturnValuesInDebugNodes() throws Exception {
      doTestShowMethodReturnValuesInDebugNodes("SWTBotLaunchDefaultPreferencesTest_testDoNotShowMethodReturnValuesInDebugNodes", false);
   }
   
   /**
    * Does the test steps of {@link #testShowMethodReturnValuesInDebugNodes()}
    * and {@link #testDoNotShowMethodReturnValuesInDebugNodes()}.
    * @param projectName The project name to use.
    * @param showMethodReturnValuesInDebugNodes Show method return values in debug node?
    * @throws Exception Occurred Exception
    */
   protected void doTestShowMethodReturnValuesInDebugNodes(String projectName, 
                                                           final boolean showMethodReturnValuesInDebugNodes) throws Exception {
      boolean originalShowMethodReturnValuesInDebugNodes = KeYSEDPreferences.isShowMethodReturnValuesInDebugNode();
      try {
         // Set preference
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         SWTBotShell preferenceShell = TestUtilsUtil.openPreferencePage(bot, "Run/Debug", "Symbolic Debug", "KeY Launch Defaults");
         if (showMethodReturnValuesInDebugNodes) {
            preferenceShell.bot().checkBox("Show method return values in debug nodes").select();
         }
         else {
            preferenceShell.bot().checkBox("Show method return values in debug nodes").deselect();
         }
         preferenceShell.bot().button("OK").click();
         assertEquals(showMethodReturnValuesInDebugNodes, KeYSEDPreferences.isShowMethodReturnValuesInDebugNode());
         // Launch something
         IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
            @Override
            public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
               // Get debug target TreeItem
               SWTBotTreeItem item = TestUtilsUtil.selectInTree(debugTree, 0, 0, 0); // Select thread
               // Do resume and test created tree
               String expectedModelPathInBundle = showMethodReturnValuesInDebugNodes ? "data/simpleIf/oracle/SimpleIf.xml" : "data/simpleIf/oracle_noMethodReturnValues/SimpleIf.xml";
               resume(bot, item, target);
               assertDebugTargetViaOracle(target, expectedModelPathInBundle, false);
            }
         };
         doKeYDebugTargetTest(projectName,
                              "data/simpleIf/test",
                              createMethodSelector("SimpleIf", "min", "I", "I"),
                              null,
                              8,
                              executor);
      }
      finally {
         // Restore original value
         KeYSEDPreferences.setShowMethodReturnValuesInDebugNode(originalShowMethodReturnValuesInDebugNodes);
         assertEquals(originalShowMethodReturnValuesInDebugNodes, KeYSEDPreferences.isShowMethodReturnValuesInDebugNode());
      }
   }
}
