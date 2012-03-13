package org.key_project.sed.key.core.test.testcase.swtbot;

import junit.framework.AssertionFailedError;
import junit.framework.TestCase;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotPerspective;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Before;
import org.junit.Test;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.sed.key.core.test.util.TestSEDKeyCoreUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Tests for the functionality of a {@link KeYDebugTarget}.
 * @author Martin Hentschel
 */
public class SWTBotKeYDebugTargetTest extends TestCase {
   /**
    * {@inheritDoc}
    */
   @Before
   @Override
   public void setUp() throws Exception {
      super.setUp();
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link ILaunch}
    * that is disconnected.
    */
   @Test
   public void testSuspendResumeWhileDisconnected_Launch() throws Exception {
      doTestSuspendResumeWhileDisconnected("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeWhileDisconnected_Launch", 
                                           0);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}
    * that is disconnected.
    */
   @Test
   public void testSuspendResumeWhileDisconnected_DebugTarget() throws Exception {
      doTestSuspendResumeWhileDisconnected("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeWhileDisconnected_DebugTarget", 
                                           0, 0);
   }
   
   /**
    * Executes the tests for {@link #testSuspendResumeWhileDisconnected_Launch()}
    * and {@link #testSuspendResumeWhileDisconnected_DebugTarget()}.
    * @param projectName The project name to use.
    * @param pathToElementInDebugTreeWhichProvidesDisconnectMenuItem The path to the element which provides the "Disconnect" menu item in the debug tree.
    * @throws Exception Occurred Exception.
    */
   protected void doTestSuspendResumeWhileDisconnected(String projectName,
                                                       int... pathToElementInDebugTreeWhichProvidesDisconnectMenuItem) throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective(bot);
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/statements", project.getProject().getFolder("src"));
         // Get method
         IMethod method = TestUtilsUtil.getJdtMethod(project, "FlatSteps", "doSomething", "I", "QString;", "Z");
         // Increase timeout
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 4;
         // Launch method
         TestSEDKeyCoreUtil.launchKeY(method);
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         ILaunch launch = target.getLaunch();
         // Test launch commands after loading completed
         assertTrue(launch.canTerminate());
         assertFalse(launch.isTerminated());
         assertTrue(target instanceof ISEDDebugTarget);
         assertTrue(target.canDisconnect());
         assertTrue(target.canResume());
         assertFalse(target.canSuspend());
         assertTrue(target.canTerminate());
         assertFalse(target.isDisconnected());
         assertTrue(target.isSuspended());
         assertFalse(target.isTerminated());
         // Make sure that the debug target is in the initial state.
         TestSEDKeyCoreUtil.assertInitialTarget(target, TestSEDKeyCoreUtil.STATEMENT_TARGET_NAME);
         // Disconnect
         SWTBotTreeItem item = TestUtilsUtil.selectInTree(debugTree, pathToElementInDebugTreeWhichProvidesDisconnectMenuItem); // Select first debug target
         item.contextMenu("Disconnect").click();
         assertTrue(launch.canTerminate());
         assertTrue(launch.isTerminated()); // Also disconnected debug targets are seen as terminated by the Eclipse Debug API.
         assertTrue(target instanceof ISEDDebugTarget);
         assertFalse(target.canDisconnect());
         assertFalse(target.canResume());
         assertFalse(target.canSuspend());
         assertTrue(target.canTerminate());
         assertTrue(target.isDisconnected());
         assertTrue(target.isSuspended());
         assertFalse(target.isTerminated());
         // Resume launch directly in KeY
         MainWindow.getInstance().getMediator().startAutoMode();
         KeYUtil.waitWhileMainWindowIsFrozen(MainWindow.getInstance());
         // Test the unmodified execution tree
         TestSEDKeyCoreUtil.assertInitialTarget(target, TestSEDKeyCoreUtil.STATEMENT_TARGET_NAME);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Restore perspective
         defaultPerspective.activate();
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget} by
    * resuming the initial state, suspend the progress and finish it
    * with a second resume.
    */
   @Test
   public void testSuspendResumeDebugTarget_Resume_Suspend_Resume() throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective(bot);
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeDebugTarget_Resume_Suspend_Resume");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/statements", project.getProject().getFolder("src"));
         // Get method
         IMethod method = TestUtilsUtil.getJdtMethod(project, "FlatSteps", "doSomething", "I", "QString;", "Z");
         // Increase timeout
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 4;
         // Launch method
         TestSEDKeyCoreUtil.launchKeY(method);
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         ILaunch launch = target.getLaunch();
         // Test launch commands after loading completed
         assertTrue(launch.canTerminate());
         assertFalse(launch.isTerminated());
         assertTrue(target instanceof ISEDDebugTarget);
         assertTrue(target.canDisconnect());
         assertTrue(target.canResume());
         assertFalse(target.canSuspend());
         assertTrue(target.canTerminate());
         assertFalse(target.isDisconnected());
         assertTrue(target.isSuspended());
         assertFalse(target.isTerminated());
         // Make sure that the debug target is in the initial state.
         TestSEDKeyCoreUtil.assertInitialTarget(target, TestSEDKeyCoreUtil.STATEMENT_TARGET_NAME);
         // Resume launch
         SWTBotTreeItem item = TestUtilsUtil.selectInTree(debugTree, 0, 0); // Select first debug target
         item.contextMenu("Resume").click();
         TestSedCoreUtil.waitUntilDebugTargetCanSuspend(bot, target); // Wait until the target is resumed.
         assertTrue(launch.canTerminate());
         assertFalse(launch.isTerminated());
         assertTrue(target.canDisconnect());
         assertFalse(target.canResume());
         assertTrue(target.canSuspend());
         assertTrue(target.canTerminate());
         assertFalse(target.isDisconnected());
         assertFalse(target.isSuspended());
         assertFalse(target.isTerminated());
         // Suspend launch
         TestSedCoreUtil.suspend(bot, target);
         // Make sure that the execution tree is not completed
         AssertionFailedError caughtError = null;
         try {
            TestSEDKeyCoreUtil.assertStatementsExample(target);
         }
         catch (AssertionFailedError e) {
            caughtError = e;
         }
         if (caughtError == null) {
            fail("Execution Tree is completed, suspend has not worked.");
         }
         // Resume launch
         item.contextMenu("Resume").click();
         TestSedCoreUtil.waitUntilDebugTargetCanSuspend(bot, target); // Wait until the target is resumed.
         assertTrue(launch.canTerminate());
         assertFalse(launch.isTerminated());
         assertTrue(target.canDisconnect());
         assertFalse(target.canResume());
         assertTrue(target.canSuspend());
         assertTrue(target.canTerminate());
         assertFalse(target.isDisconnected());
         assertFalse(target.isSuspended());
         assertFalse(target.isTerminated());
         TestSedCoreUtil.waitUntilDebugTargetCanResume(bot, target); // wait until the target is suspended.
         assertTrue(launch.canTerminate());
         assertFalse(launch.isTerminated());
         assertTrue(target.canDisconnect());
         assertTrue(target.canResume());
         assertFalse(target.canSuspend());
         assertTrue(target.canTerminate());
         assertFalse(target.isDisconnected());
         assertTrue(target.isSuspended());
         assertFalse(target.isTerminated());
         // Test the execution tree
         TestSEDKeyCoreUtil.assertStatementsExample(target);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Restore perspective
         defaultPerspective.activate();
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testSuspendResumeDebugTarget_Resume() throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective(bot);
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeDebugTarget_Resume");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/statements", project.getProject().getFolder("src"));
         // Get method
         IMethod method = TestUtilsUtil.getJdtMethod(project, "FlatSteps", "doSomething", "I", "QString;", "Z");
         // Increase timeout
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 4;
         // Launch method
         TestSEDKeyCoreUtil.launchKeY(method);
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         ILaunch launch = target.getLaunch();
         // Test launch commands after loading completed
         assertTrue(launch.canTerminate());
         assertFalse(launch.isTerminated());
         assertTrue(target instanceof ISEDDebugTarget);
         assertTrue(target.canDisconnect());
         assertTrue(target.canResume());
         assertFalse(target.canSuspend());
         assertTrue(target.canTerminate());
         assertFalse(target.isDisconnected());
         assertTrue(target.isSuspended());
         assertFalse(target.isTerminated());
         // Make sure that the debug target is in the initial state.
         TestSEDKeyCoreUtil.assertInitialTarget(target, TestSEDKeyCoreUtil.STATEMENT_TARGET_NAME);
         // Resume launch
         SWTBotTreeItem item = TestUtilsUtil.selectInTree(debugTree, 0, 0); // Select first debug target
         item.contextMenu("Resume").click();
         TestSedCoreUtil.waitUntilDebugTargetCanSuspend(bot, target); // Wait until the target is resumed.
         assertTrue(launch.canTerminate());
         assertFalse(launch.isTerminated());
         assertTrue(target.canDisconnect());
         assertFalse(target.canResume());
         assertTrue(target.canSuspend());
         assertTrue(target.canTerminate());
         assertFalse(target.isDisconnected());
         assertFalse(target.isSuspended());
         assertFalse(target.isTerminated());
         TestSedCoreUtil.waitUntilDebugTargetCanResume(bot, target); // wait until the target is suspended.
         assertTrue(launch.canTerminate());
         assertFalse(launch.isTerminated());
         assertTrue(target.canDisconnect());
         assertTrue(target.canResume());
         assertFalse(target.canSuspend());
         assertTrue(target.canTerminate());
         assertFalse(target.isDisconnected());
         assertTrue(target.isSuspended());
         assertFalse(target.isTerminated());
         // Test the execution tree
         TestSEDKeyCoreUtil.assertStatementsExample(target);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Restore perspective
         defaultPerspective.activate();
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
   }

   /**
    * Tests the termination functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testTerminationDebugTarget() throws Exception {
      doTerminationTest("SWTBotKeYDebugTargetTerminationTest_testTerminationDebugTarget", 0, 0);
   }

   /**
    * Tests the termination functionality on the {@link ILaunch}.
    */
   @Test
   public void testTerminationLaunch() throws Exception {
      doTerminationTest("SWTBotKeYDebugTargetTerminationTest_testTerminationLaunch", 0);
   }
   
   /**
    * Executes the test for {@link #testTerminationDebugTarget()} and
    * {@link #testTerminationLaunch()}.
    * @param projectName The project name to use.
    * @param pathToElementInDebugTreeWhichProvidesTerminateMenuItem The path to the element which provides the "Terminate" menu item in the debug tree.
    * @throws Exception Occurred Exception.
    */
   protected void doTerminationTest(String projectName,
                                    int... pathToElementInDebugTreeWhichProvidesTerminateMenuItem) throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective(bot);
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/statements", project.getProject().getFolder("src"));
         // Get method
         IMethod method = TestUtilsUtil.getJdtMethod(project, "FlatSteps", "doSomething", "I", "QString;", "Z");
         // Increase timeout
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 8;
         // Launch method
         TestSEDKeyCoreUtil.launchKeY(method);
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         IDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         ILaunch launch = target.getLaunch();
         // Test launch commands after loading completed
         assertTrue(launch.canTerminate());
         assertFalse(launch.isTerminated());
         assertTrue(target instanceof ISEDDebugTarget);
         assertTrue(target.canDisconnect());
         assertTrue(target.canResume());
         assertFalse(target.canSuspend());
         assertTrue(target.canTerminate());
         assertFalse(target.isDisconnected());
         assertTrue(target.isSuspended());
         assertFalse(target.isTerminated());
         // Terminate launch
         SWTBotTreeItem item = TestUtilsUtil.selectInTree(debugTree, pathToElementInDebugTreeWhichProvidesTerminateMenuItem); // Select first launch
         item.contextMenu("Terminate").click();
         TestSedCoreUtil.waitUntilLaunchIsTerminated(bot, launch);
         assertFalse(launch.canTerminate());
         assertTrue(launch.isTerminated());
         assertFalse(target.canDisconnect());
         assertFalse(target.canResume());
         assertFalse(target.canSuspend());
         assertFalse(target.canTerminate());
         assertFalse(target.isDisconnected());
         assertTrue(target.isSuspended());
         assertTrue(target.isTerminated());
         // Remove terminated launch
         item.contextMenu("Remove All Terminated").click();
         assertEquals(0, debugTree.getAllItems().length);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Restore perspective
         defaultPerspective.activate();
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
   }
}
