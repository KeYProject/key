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
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
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
import de.uka.ilkd.key.proof.Proof;

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
   public void testMethodCallFormatTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallFormatTest",
                     "data/methodFormatTest",
                     false,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "MethodFormatTest", "main");
                        }
                     },
                     TestSEDKeyCoreUtil.METHOD_CALL_FORMAT_TEST_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedMethodCallFormatTestModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFixedRecursiveMethodCall() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testFixedRecursiveMethodCall",
                     "data/fixedRecursiveMethodCallTest",
                     false,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "FixedRecursiveMethodCallTest", "decreaseValue");
                        }
                     },
                     TestSEDKeyCoreUtil.FIXED_RECURSIVE_METHOD_CALL_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedFixedRecursiveMethodCallModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testElseIfDifferentVariables() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testElseIfDifferentVariables",
                     "data/elseIfDifferentVariables",
                     false,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "ElseIfDifferentVariables", "main", "Z", "Z");
                        }
                     },
                     TestSEDKeyCoreUtil.ELSE_IF_DIFFERENT_VARIABLES_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedElseIfDifferentVariablesModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testTryCatchFinally() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testTryCatchFinally",
                     "data/tryCatchFinally",
                     false,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "TryCatchFinally", "tryCatchFinally", "I");
                        }
                     },
                     TestSEDKeyCoreUtil.TRY_CATCH_FINALLY_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedTryCatchFinallyModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testStaticMethodCall() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testStaticMethodCall",
                     "data/staticMethodCall",
                     false,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "StaticMethodCall", "main");
                        }
                     },
                     TestSEDKeyCoreUtil.STATIC_METHOD_CALL_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedStaticMethodCallModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testComplexIfSteps() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testComplexIfSteps",
                     "data/complexIf",
                     false,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "ComplexIf", "min", "I", "I");
                        }
                     },
                     TestSEDKeyCoreUtil.COMPLEX_IF_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedComplexIfModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testComplexFlatSteps() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testComplexFlatSteps",
                     "data/complexFlatSteps",
                     false,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "ComplexFlatSteps", "doSomething");
                        }
                     },
                     TestSEDKeyCoreUtil.COMPLEX_FLAT_STEPS_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedComplexFlatStepsModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFunctionalIf() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testFunctionalIf",
                     "data/functionalIf",
                     false,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "FunctionalIf", "min", "I", "I");
                        }
                     },
                     TestSEDKeyCoreUtil.FUNCTIONAL_IF_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedFunctionalIfModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testSimpleIf() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testSimpleIf",
                     "data/simpleIf",
                     false,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "SimpleIf", "min", "I", "I");
                        }
                     },
                     TestSEDKeyCoreUtil.SIMPLE_IF_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedSimpleIfModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallOnObjectWithException() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallOnObjectWithException",
                     "data/methodCallOnObjectWithException",
                     false,
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
                     false,
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
                     false,
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
                     false,
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
                     false,
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
         TestSedCoreUtil.openSymbolicDebugPerspective();
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
         TestSEDKeyCoreUtil.assertInitialTarget(target, TestSEDKeyCoreUtil.FLAT_STEPS_TARGET_NAME);
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
            TestSEDKeyCoreUtil.assertFlatStepsExample(target);
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
         TestSEDKeyCoreUtil.assertFlatStepsExample(target);
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
                     false,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "FlatSteps", "doSomething", "I", "QString;", "Z");
                        }
                     },
                     TestSEDKeyCoreUtil.FLAT_STEPS_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedFlatStepsModel());
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget},
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testFlatStatements_ProofIsNoLongerAvailableInKeY() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testFlatStatements_ProofIsNoLongerAvailableInKeY",
                     "data/statements",
                     true,
                     new IMethodSelector() {
                        @Override
                        public IMethod getMethod(IJavaProject project) throws Exception {
                           return TestUtilsUtil.getJdtMethod(project, "FlatSteps", "doSomething", "I", "QString;", "Z");
                        }
                     },
                     TestSEDKeyCoreUtil.FLAT_STEPS_TARGET_NAME,
                     TestSEDKeyCoreUtil.createExpectedFlatStepsModel());
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
    * @param clearProofListInKeYBeforeResume Clear proof list in KeY before resume?
    * @param selector {@link IMethodSelector} to select an {@link IMethod} to launch.
    * @param targetName The name of the {@link IDebugTarget}.
    * @param expectedDebugTarget The expected {@link ISEDDebugTarget}.
    * @throws Exception Occurred Exception.
    */
   protected void assertSEDModel(String projectName,
                                 String pathInBundle,
                                 boolean clearProofListInKeYBeforeResume,
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
         TestSedCoreUtil.openSymbolicDebugPerspective();
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathInBundle, project.getProject().getFolder("src"));
         // Get method
         assertNotNull(selector);
         IMethod method = selector.getMethod(project);
         // Increase timeout
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 8;
         // Store original settings of KeY which requires that at least one proof was instantiated.
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
         // Get debug target TreeItem
         SWTBotTreeItem item = TestUtilsUtil.selectInTree(debugTree, 0, 0); // Select first debug target
         SWTBotMenu menuItem = item.contextMenu("Resume"); 
         // Remove proof in KeY if required
         if (clearProofListInKeYBeforeResume) {
            assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
            KeYUtil.clearProofList(MainWindow.getInstance());
            assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
         }
         // Resume launch
         menuItem.click();
         if (clearProofListInKeYBeforeResume) {
            assertTrue(launch.canTerminate());
            assertFalse(launch.isTerminated());
            assertTrue(target.canDisconnect());
            assertFalse(target.canSuspend());
            assertTrue(target.canTerminate());
            assertFalse(target.isDisconnected());
            assertTrue(target.isSuspended());
            assertFalse(target.isTerminated());
            assertFalse(target.canResume());
            // Test the execution tree
            TestSEDKeyCoreUtil.assertInitialTarget(target, targetName);
         }
         else {
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
            assertFalse(target.canSuspend());
            assertTrue(target.canTerminate());
            assertFalse(target.isDisconnected());
            assertTrue(target.isSuspended());
            assertFalse(target.isTerminated());
            assertTrue(target.canResume());
            // Test the execution tree
            TestSEDKeyCoreUtil.compareDebugTarget(expectedDebugTarget, target);
         }
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
                                           false,
                                           0);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}
    * that is disconnected.
    */
   @Test
   public void testSuspendResumeWhileDisconnected_DebugTarget() throws Exception {
      doTestSuspendResumeWhileDisconnected("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeWhileDisconnected_DebugTarget",
                                           false,
                                           0, 0);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link ILaunch}
    * that is disconnected,
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testSuspendResumeWhileDisconnected_Launch_ProofIsNoLongerAvailableInKeY() throws Exception {
      doTestSuspendResumeWhileDisconnected("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeWhileDisconnected_Launch_ProofIsNoLongerAvailableInKeY",
                                           true,
                                           0);
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}
    * that is disconnected,
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testSuspendResumeWhileDisconnected_DebugTarget_ProofIsNoLongerAvailableInKeY() throws Exception {
      doTestSuspendResumeWhileDisconnected("SWTBotKeYDebugTargetSuspendResumeTest_testSuspendResumeWhileDisconnected_DebugTarget_ProofIsNoLongerAvailableInKeY",
                                           true,
                                           0, 0);
   }
   
   /**
    * Executes the tests for {@link #testSuspendResumeWhileDisconnected_Launch()}
    * and {@link #testSuspendResumeWhileDisconnected_DebugTarget()}.
    * @param projectName The project name to use.
    * @param clearProofListInKeYBeforeDisconnect Clear proof list in KeY before disconnecting the {@link ILaunch}?
    * @param pathToElementInDebugTreeWhichProvidesDisconnectMenuItem The path to the element which provides the "Disconnect" menu item in the debug tree.
    * @throws Exception Occurred Exception.
    */
   protected void doTestSuspendResumeWhileDisconnected(String projectName,
                                                       boolean clearProofListInKeYBeforeDisconnect,
                                                       int... pathToElementInDebugTreeWhichProvidesDisconnectMenuItem) throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
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
         TestSEDKeyCoreUtil.assertInitialTarget(target, TestSEDKeyCoreUtil.FLAT_STEPS_TARGET_NAME);
         // Clear proof list in KeY if required
         if (clearProofListInKeYBeforeDisconnect) {
            assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
            KeYUtil.clearProofList(MainWindow.getInstance());
            assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
         }
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
         if (!clearProofListInKeYBeforeDisconnect) {
            MainWindow.getInstance().getMediator().startAutoMode();
            KeYUtil.waitWhileMainWindowIsFrozen(MainWindow.getInstance());
         }
         // Test the unmodified execution tree
         TestSEDKeyCoreUtil.assertInitialTarget(target, TestSEDKeyCoreUtil.FLAT_STEPS_TARGET_NAME);
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
      doTerminationTest("SWTBotKeYDebugTargetTerminationTest_testTerminationDebugTarget", false, 0, 0);
   }

   /**
    * Tests the termination functionality on the {@link ILaunch}.
    */
   @Test
   public void testTerminationLaunch() throws Exception {
      doTerminationTest("SWTBotKeYDebugTargetTerminationTest_testTerminationLaunch", false, 0);
   }

   /**
    * Tests the termination functionality on the {@link IDebugTarget},
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testTerminationDebugTarget_ProofIsNoLongerAvailableInKeY() throws Exception {
      doTerminationTest("SWTBotKeYDebugTargetTerminationTest_testTerminationDebugTarget_ProofIsNoLongerAvailableInKeY", true, 0, 0);
   }

   /**
    * Tests the termination functionality on the {@link ILaunch},
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testTerminationLaunch_ProofIsNoLongerAvailableInKeY() throws Exception {
      doTerminationTest("SWTBotKeYDebugTargetTerminationTest_testTerminationLaunch_ProofIsNoLongerAvailableInKeY", true, 0);
   }
   
   /**
    * Executes the test for {@link #testTerminationDebugTarget()} and
    * {@link #testTerminationLaunch()}.
    * @param projectName The project name to use.
    * @param clearProofListInKeYBeforeTermination Clear proof list before terminating the {@link ILaunch}?
    * @param pathToElementInDebugTreeWhichProvidesTerminateMenuItem The path to the element which provides the "Terminate" menu item in the debug tree.
    * @throws Exception Occurred Exception.
    */
   protected void doTerminationTest(String projectName,
                                    boolean clearProofListInKeYBeforeTermination,
                                    int... pathToElementInDebugTreeWhichProvidesTerminateMenuItem) throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
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
         // Remove proof in KeY if required
         if (clearProofListInKeYBeforeTermination) {
            assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
            KeYUtil.clearProofList(MainWindow.getInstance());
            assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
         }
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
