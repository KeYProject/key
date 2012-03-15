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
import org.key_project.key4eclipse.starter.core.test.util.TestStarterCoreUtil;
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
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallOnObjectWithException() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallOnObjectWithException",
                     "data/methodCallOnObjectWithException",
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "MethodCallOnObjectWithException", "main");
                        }
                     },
                     TestSEDKeyCoreUtil.METHOD_CALL_ON_OBJECT_WITH_EXCEPTION_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedMethodCallOnObjectWithExceptionModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallOnObject() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallOnObject",
                     "data/methodCallOnObject",
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "MethodCallOnObject", "main");
                        }
                     },
                     TestSEDKeyCoreUtil.METHOD_CALL_ON_OBJECT_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedMethodCallOnObjectModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallParallel() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallParallel",
                     "data/methodCallParallelTest",
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "MethodCallParallelTest", "main");
                        }
                     },
                     TestSEDKeyCoreUtil.METHOD_CALL_PARALLEL_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedMethodCallParallelModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallHierarchyWithException() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallHierarchyWithException",
                     "data/methodHierarchyCallWithExceptionTest",
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "MethodHierarchyCallWithExceptionTest", "main");
                        }
                     },
                     TestSEDKeyCoreUtil.METHOD_CALL_HIERARCHY_WITH_EXCEPTION_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedMethodCallHierarchyWithExceptionModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallHierarchy() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallHierarchy",
                     "data/methodHierarchyCallTest",
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "MethodHierarchyCallTest", "main");
                        }
                     },
                     TestSEDKeyCoreUtil.METHOD_CALL_HIERARCHY_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedMethodCallHierarchyModel());
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
   public void testFlatStatements() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testFlatStatements",
                     "data/statements",
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "FlatSteps", "doSomething", "I", "QString;", "Z");
                        }
                     },
                     TestSEDKeyCoreUtil.STATEMENT_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedStatementModel());
   }
   
   /**
    * Utility class to select an {@link IMethod} in a given {@link IJavaProject}.
    * @author Martin Hentschel
    */
   public static interface IMethodSelector {
      /**
       * Selects an {@link IMethod} in the given {@link IJavaProject}.
       * @param project The {@link IJavaProject}.
       * @return The selected {@link IMethod}.
       * @throws Exception Occurred Exceptions.
       */
      public IMethod getMethod(IJavaProject project) throws Exception;
   }
   
   /**
    * Executes the following test steps:
    * <ol>
    *    <li>Extract code from bundle to a Java project with the defined name in the workspace.</li>
    *    <li>Select an {@link IMethod} to debug with the given {@link IMethodSelector}.</li>
    *    <li>Launch selected {@link IMethod} with the Symbolic Execution Debugger based on KeY.</li>
    *    <li>Make sure that the initial SED model ({@link ISEDDebugTarget}) is opened.</li>
    *    <li>Resume the execution.</li>
    *    <li>Make sure that the final SED model ({@link ISEDDebugTarget}) specified by the given {@link ISEDDebugTarget} is reached.</li>
    * </ol>
    * @param projectName The project name in the workspace.
    * @param pathInBundle The path to the source code in the bundle to extract to the workspace project.
    * @param selector {@link IMethodSelector} to select an {@link IMethod} to launch.
    * @param targetName The name of the {@link IDebugTarget}.
    * @param expectedDebugTarget The expected {@link ISEDDebugTarget}.
    * @throws Exception Occurred Exception.
    */
   protected void assertSEDModel(String projectName,
                                 String pathInBundle,
                                 IMethodSelector selector,
                                 String targetName,
                                 ISEDDebugTarget expectedDebugTarget) throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      String originalRuntimeExceptions = null;
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective(bot);
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathInBundle, project.getProject().getFolder("src"));
         // Get method
         assertNotNull(selector);
         IMethod method = selector.getMethod(project);
         // Increase timeout
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 8;
         // Store original settings of KeY which requires that at least one proof was intantiated.
         if (!KeYUtil.isChoiceSettingInitialised()) {
            TestStarterCoreUtil.instantiateProofWithGeneratedContract(method);
            KeYUtil.clearProofList(MainWindow.getInstance());
         }
         originalRuntimeExceptions = KeYUtil.getChoiceSetting(KeYUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);
         assertNotNull(originalRuntimeExceptions);
         // Set choice settings in KeY.
         KeYUtil.setChoiceSetting(KeYUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, KeYUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW);
         assertEquals(KeYUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW, KeYUtil.getChoiceSetting(KeYUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS));
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
         TestSEDKeyCoreUtil.assertInitialTarget(target, targetName);
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
         TestSEDKeyCoreUtil.compareDebugTarget(expectedDebugTarget, target);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Restore runtime option
         if (originalRuntimeExceptions != null) {
            KeYUtil.setChoiceSetting(KeYUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalRuntimeExceptions);
         }
         // Restore perspective
         defaultPerspective.activate();
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
      }
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
