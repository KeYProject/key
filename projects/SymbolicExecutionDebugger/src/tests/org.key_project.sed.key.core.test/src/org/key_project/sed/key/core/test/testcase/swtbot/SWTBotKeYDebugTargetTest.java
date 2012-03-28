package org.key_project.sed.key.core.test.testcase.swtbot;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import junit.framework.AssertionFailedError;
import junit.framework.TestCase;

import org.eclipse.debug.core.DebugException;
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
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.sed.key.core.test.util.TestSEDKeyCoreUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;

/**
 * Tests for the functionality of a {@link KeYDebugTarget}.
 * @author Martin Hentschel
 */
public class SWTBotKeYDebugTargetTest extends TestCase {
   /**
    * <p>
    * If this constant is {@code true} a temporary directory is created with
    * new oracle files. The developer has than to copy the new required files
    * into the plug-in so that they are used during next test execution.
    * </p>
    * <p>
    * <b>Attention: </b> It is strongly required that new test scenarios
    * are verified with the SED application. If everything is fine a new test
    * method can be added to this class and the first test execution can be
    * used to generate the required oracle file. Existing oracle files should
    * only be replaced if the functionality of the Symbolic Execution Debugger
    * has changed so that they are outdated.
    * </p>
    */
   public static final boolean CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY = false;
   
   /**
    * The used temporary oracle directory.
    */
   private static final File oracleDirectory;

   /**
    * Creates the temporary oracle directory if required.
    */
   static {
      File directory = null;
      try {
         if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            directory = IOUtil.createTempDirectory("ORACLE_DIRECTORY", StringUtil.EMPTY_STRING);
         }
      }
      catch (IOException e) {
      }
      oracleDirectory = directory;
   }
   
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
   public void testSwitchCase() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testSwitchCase",
                     "data/switchCaseTest/test",
                     false,
                     createMethodSelector("SwitchCaseTest", "switchCase", "I"),
                     "data/switchCaseTest/oracle/SwitchCaseTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testElseIf() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testElseIf",
                     "data/elseIfTest/test",
                     false,
                     createMethodSelector("ElseIfTest", "elseIf", "I"),
                     "data/elseIfTest/oracle/ElseIfTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallFormatTest() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallFormatTest",
                     "data/methodFormatTest/test",
                     false,
                     createMethodSelector("MethodFormatTest", "main"),
                     "data/methodFormatTest/oracle/MethodFormatTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFixedRecursiveMethodCall() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testFixedRecursiveMethodCall",
                     "data/fixedRecursiveMethodCallTest/test",
                     false,
                     createMethodSelector("FixedRecursiveMethodCallTest", "decreaseValue"),
                     "data/fixedRecursiveMethodCallTest/oracle/FixedRecursiveMethodCallTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testElseIfDifferentVariables() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testElseIfDifferentVariables",
                     "data/elseIfDifferentVariables/test",
                     false,
                     createMethodSelector("ElseIfDifferentVariables", "main", "Z", "Z"),
                     "data/elseIfDifferentVariables/oracle/ElseIfDifferentVariables.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testTryCatchFinally() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testTryCatchFinally",
                     "data/tryCatchFinally/test",
                     false,
                     createMethodSelector("TryCatchFinally", "tryCatchFinally", "I"),
                     "data/tryCatchFinally/oracle/TryCatchFinally.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testStaticMethodCall() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testStaticMethodCall",
                     "data/staticMethodCall/test",
                     false,
                     createMethodSelector("StaticMethodCall", "main"),
                     "data/staticMethodCall/oracle/StaticMethodCall.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testComplexIfSteps() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testComplexIfSteps",
                     "data/complexIf/test",
                     false,
                     createMethodSelector("ComplexIf", "min", "I", "I"),
                     "data/complexIf/oracle/ComplexIf.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testComplexFlatSteps() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testComplexFlatSteps",
                     "data/complexFlatSteps/test",
                     false,
                     createMethodSelector("ComplexFlatSteps", "doSomething"),
                     "data/complexFlatSteps/oracle/ComplexFlatSteps.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testFunctionalIf() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testFunctionalIf",
                     "data/functionalIf/test",
                     false,
                     createMethodSelector("FunctionalIf", "min", "I", "I"),
                     "data/functionalIf/oracle/FunctionalIf.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testSimpleIf() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testSimpleIf",
                     "data/simpleIf/test",
                     false,
                     createMethodSelector("SimpleIf", "min", "I", "I"),
                     "data/simpleIf/oracle/SimpleIf.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallOnObjectWithException() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallOnObjectWithException",
                     "data/methodCallOnObjectWithException/test",
                     false,
                     createMethodSelector("MethodCallOnObjectWithException", "main"),
                     "data/methodCallOnObjectWithException/oracle/MethodCallOnObjectWithException.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallOnObject() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallOnObject",
                     "data/methodCallOnObject/test",
                     false,
                     createMethodSelector("MethodCallOnObject", "main"),
                     "data/methodCallOnObject/oracle/MethodCallOnObject.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallParallel() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallParallel",
                     "data/methodCallParallelTest/test",
                     false,
                     createMethodSelector("MethodCallParallelTest", "main"),
                     "data/methodCallParallelTest/oracle/MethodCallParallelTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallHierarchyWithException() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallHierarchyWithException",
                     "data/methodHierarchyCallWithExceptionTest/test",
                     false,
                     createMethodSelector("MethodHierarchyCallWithExceptionTest", "main"),
                     "data/methodHierarchyCallWithExceptionTest/oracle/MethodHierarchyCallWithExceptionTest.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget}.
    */
   @Test
   public void testMethodCallHierarchy() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testMethodCallHierarchy",
                     "data/methodHierarchyCallTest/test",
                     false,
                     createMethodSelector("MethodHierarchyCallTest", "main"),
                     "data/methodHierarchyCallTest/oracle/MethodHierarchyCallTest.xml");
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
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/statements/test", project.getProject().getFolder("src"));
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
         TestSEDKeyCoreUtil.assertInitialTarget(target, TestSEDKeyCoreUtil.computeTargetName(method));
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
                     "data/statements/test",
                     false,
                     createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"),
                     "data/statements/oracle/FlatSteps.xml");
   }
   
   /**
    * Tests the suspend/resume functionality on the {@link IDebugTarget},
    * but the {@link Proof} is already removed in KeY.
    */
   @Test
   public void testFlatStatements_ProofIsNoLongerAvailableInKeY() throws Exception {
      assertSEDModel("SWTBotKeYDebugTargetSuspendResumeTest_testFlatStatements_ProofIsNoLongerAvailableInKeY",
                     "data/statements/test",
                     true,
                     createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"),
                     "data/statements/oracle/FlatSteps.xml");
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
    * Creates a default {@link IMethodSelector} which uses
    * {@link TestUtilsUtil#getJdtMethod(IJavaProject, String, String, String...)}
    * to select an {@link IMethod}.
    * @param typeName The type name.
    * @param methodName The method name.
    * @param parameters The method parameters.
    * @return The created {@link IMethodSelector}.
    */
   public static IMethodSelector createMethodSelector(final String typeName, 
                                                      final String methodName, 
                                                      final String... parameters) {
      return new IMethodSelector() {
         @Override
         public IMethod getMethod(IJavaProject project) throws Exception {
            return TestUtilsUtil.getJdtMethod(project, typeName, methodName, parameters);
         }
      };
   }
   
   /**
    * Executes the following test steps:
    * <ol>
    *    <li>Extract code from bundle to a Java project with the defined name in the workspace.</li>
    *    <li>Select an {@link IMethod} to debug with the given {@link IMethodSelector}.</li>
    *    <li>Launch selected {@link IMethod} with the Symbolic Execution Debugger based on KeY.</li>
    *    <li>Make sure that the initial SED model ({@link ISEDDebugTarget}) is opened.</li>
    *    <li>Resume the execution.</li>
    *    <li>Make sure that the final SED model ({@link ISEDDebugTarget}) specified by the oracle file expectedModelPathInBundle is reached.</li>
    * </ol>
    * @param projectName The project name in the workspace.
    * @param pathInBundle The path to the source code in the bundle to extract to the workspace project.
    * @param clearProofListInKeYBeforeResume Clear proof list in KeY before resume?
    * @param selector {@link IMethodSelector} to select an {@link IMethod} to launch.
    * @param expectedModelPathInBundle Path to the oracle file in the bundle which defines the expected {@link ISEDDebugTarget} model.
    * @throws Exception Occurred Exception.
    */
   protected void assertSEDModel(String projectName,
                                 String pathInBundle,
                                 boolean clearProofListInKeYBeforeResume,
                                 IMethodSelector selector,
                                 String expectedModelPathInBundle) throws Exception {
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
         String targetName = TestSEDKeyCoreUtil.computeTargetName(method);
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
            if (oracleDirectory != null) {
               createOracleFile(target, expectedModelPathInBundle);
            }
            ISEDDebugTarget expectedDebugTarget = TestSEDKeyCoreUtil.createExpectedModel(expectedModelPathInBundle);
            TestSedCoreUtil.compareDebugTarget(expectedDebugTarget, target);
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
    * Creates a new oracle file for the given {@link ISEDDebugTarget}.
    * @param target The given {@link ISEDDebugTarget} which provides the oracle data.
    * @param expectedModelPathInBundle The path in the bundle under that the created oracle file will be later available. It is used to create sub directories in temp directory.
    * @throws IOException Occurred Exception.
    * @throws DebugException Occurred Exception.
    */
   protected void createOracleFile(ISEDDebugTarget target, String expectedModelPathInBundle) throws IOException, DebugException {
      if (oracleDirectory != null && oracleDirectory.isDirectory()) {
         // Create sub folder structure
         File oracleFile = new File(oracleDirectory, expectedModelPathInBundle);
         oracleFile.getParentFile().mkdirs();
         // Create oracle file
         SEDXMLWriter writer = new SEDXMLWriter();
         writer.write(target.getLaunch(), SEDXMLWriter.DEFAULT_ENCODING, new FileOutputStream(oracleFile));
         // Print message to the user.
         printOracleDirectory();
      }
   }
   
   /**
    * Prints {@link #oracleDirectory} to the user via {@link System#out}.
    */
   protected void printOracleDirectory() {
      if (oracleDirectory != null) {
         final String HEADER_LINE = "Oracle Directory is:";
         final String PREFIX = "### ";
         final String SUFFIX = " ###";
         String path = oracleDirectory.toString();
         int length = Math.max(path.length(), HEADER_LINE.length());
         String borderLines = StringUtil.createLine("#", PREFIX.length() + length + SUFFIX.length());
         System.out.println(borderLines);
         System.out.println(PREFIX + HEADER_LINE + StringUtil.createLine(" ", length - HEADER_LINE.length()) + SUFFIX);
         System.out.println(PREFIX + path + StringUtil.createLine(" ", length - path.length()) + SUFFIX);
         System.out.println(borderLines);
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
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/statements/test", project.getProject().getFolder("src"));
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
         String targetName = TestSEDKeyCoreUtil.computeTargetName(method);
         TestSEDKeyCoreUtil.assertInitialTarget(target, targetName);
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
         TestSEDKeyCoreUtil.assertInitialTarget(target, targetName);
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
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/statements/test", project.getProject().getFolder("src"));
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
