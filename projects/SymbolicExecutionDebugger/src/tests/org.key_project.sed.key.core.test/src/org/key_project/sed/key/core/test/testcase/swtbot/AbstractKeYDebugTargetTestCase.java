package org.key_project.sed.key.core.test.testcase.swtbot;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;

import junit.framework.TestCase;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IStep;
import org.eclipse.debug.core.model.ISuspendResume;
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
import org.xml.sax.SAXException;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Provides the functionality to test {@link KeYDebugTarget}s.
 * @author Martin Hentschel
 */
public class AbstractKeYDebugTargetTestCase extends TestCase {
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
    * Creates a new oracle file for the given {@link ISEDDebugTarget}.
    * @param target The given {@link ISEDDebugTarget} which provides the oracle data.
    * @param expectedModelPathInBundle The path in the bundle under that the created oracle file will be later available. It is used to create sub directories in temp directory.
    * @param saveVariables Save variables?
    * @throws IOException Occurred Exception.
    * @throws DebugException Occurred Exception.
    */
   protected static void createOracleFile(ISEDDebugTarget target, 
                                          String expectedModelPathInBundle, 
                                          boolean saveVariables) throws IOException, DebugException {
      if (oracleDirectory != null && oracleDirectory.isDirectory()) {
         // Create sub folder structure
         File oracleFile = new File(oracleDirectory, expectedModelPathInBundle);
         oracleFile.getParentFile().mkdirs();
         // Create oracle file
         SEDXMLWriter writer = new SEDXMLWriter();
         writer.write(target.getLaunch(), SEDXMLWriter.DEFAULT_ENCODING, new FileOutputStream(oracleFile), saveVariables);
         // Print message to the user.
         printOracleDirectory();
      }
   }
   
   /**
    * Prints {@link #oracleDirectory} to the user via {@link System#out}.
    */
   protected static void printOracleDirectory() {
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
    * Returns the oracle directory.
    * @return The oracle directory.
    */
   public static File getOracledirectory() {
      return oracleDirectory;
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
    * makes sure that the given {@link ISEDDebugTarget} contains the
    * same model as defined by the oracle file.
    * @param target The {@link ISEDDebugTarget} to test.
    * @param expectedModelPathInBundle The expected path to the oracle file.
    * @param includeVariables Include variables?
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    */
   protected static void assertDebugTargetViaOracle(ISEDDebugTarget target,
                                                    String expectedModelPathInBundle,
                                                    boolean includeVariables) throws DebugException, IOException, ParserConfigurationException, SAXException {
      createOracleFile(target, expectedModelPathInBundle, includeVariables);
      if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
         ISEDDebugTarget expectedDebugTarget = TestSEDKeyCoreUtil.createExpectedModel(expectedModelPathInBundle);
         TestSedCoreUtil.compareDebugTarget(expectedDebugTarget, target, false, includeVariables);
      }
   }
   
   /**
    * Makes sure that one test step is correctly done.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param expectedModelPathInBundle The path and file name of oracle file.
    * @param modelIndex The index of the oracle file.
    * @param expectedModelFileExtension The oracle file extension.
    * @throws DebugException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected static void assertStep(ISEDDebugTarget target,
                                    String expectedModelPathInBundle,
                                    int modelIndex,
                                    String expectedModelFileExtension) throws DebugException, IOException, ParserConfigurationException, SAXException {
      assertDebugTargetViaOracle(target, expectedModelPathInBundle + modelIndex + expectedModelFileExtension, false);
   }
   
   /**
    * Makes sure that a step into was done correctly.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step into on.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param expectedModelPathInBundle The path and file name of oracle file.
    * @param modelIndex The index of the oracle file.
    * @param expectedModelFileExtension The oracle file extension.
    * @throws DebugException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected void assertStepInto(SWTWorkbenchBot bot, 
                                 SWTBotTreeItem launchTreeItem, 
                                 ISEDDebugTarget target,
                                 String expectedModelPathInBundle,
                                 int modelIndex,
                                 String expectedModelFileExtension) throws DebugException, IOException, ParserConfigurationException, SAXException {
      stepInto(bot, launchTreeItem, target);
      assertStep(target, expectedModelPathInBundle, modelIndex, expectedModelFileExtension);
   }
   
   /**
    * Performs a step into on the given {@link SWTBotTreeItem}.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step into on.
    * @param target The {@link ISEDDebugTarget} to use.
    */
   protected static void stepInto(SWTWorkbenchBot bot, 
                                  SWTBotTreeItem launchTreeItem, 
                                  ISEDDebugTarget target) {
      assertNotNull(bot);
      assertNotNull(launchTreeItem);
      assertNotNull(target);
      Object leafData = TestUtilsUtil.getTreeItemData(launchTreeItem);
      if (leafData instanceof IStep) {
         IStep leafStep = (IStep)leafData;
         assertTrue(leafStep.canStepInto());
         launchTreeItem.select();
         SWTBotMenu menuItem = launchTreeItem.contextMenu("Step Into"); 
         menuItem.click();
         TestSedCoreUtil.waitUntilDebugTargetCanSuspend(bot, target); // Wait until the target is resumed.
         assertFalse(leafStep.canStepInto());
         TestSedCoreUtil.waitUntilDebugTargetCanResume(bot, target); // wait until the target is suspended.
         assertTrue(leafStep.canStepInto());
      }
   }
   
   /**
    * Makes sure that a step over was done correctly.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step over on.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param expectedModelPathInBundle The path and file name of oracle file.
    * @param modelIndex The index of the oracle file.
    * @param expectedModelFileExtension The oracle file extension.
    * @throws DebugException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected void assertStepOver(SWTWorkbenchBot bot, 
                                 SWTBotTreeItem launchTreeItem, 
                                 ISEDDebugTarget target,
                                 String expectedModelPathInBundle,
                                 int modelIndex,
                                 String expectedModelFileExtension) throws DebugException, IOException, ParserConfigurationException, SAXException {
      stepOver(bot, launchTreeItem, target);
      assertStep(target, expectedModelPathInBundle, modelIndex, expectedModelFileExtension);
   }
   
   /**
    * Performs a step over on the given {@link SWTBotTreeItem}.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step over on.
    * @param target The {@link ISEDDebugTarget} to use.
    */
   protected static void stepOver(SWTWorkbenchBot bot, 
                                  SWTBotTreeItem launchTreeItem, 
                                  ISEDDebugTarget target) {
      assertNotNull(bot);
      assertNotNull(launchTreeItem);
      assertNotNull(target);
      Object leafData = TestUtilsUtil.getTreeItemData(launchTreeItem);
      if (leafData instanceof IStep) {
         IStep leafStep = (IStep)leafData;
         assertTrue(leafStep.canStepOver());
         launchTreeItem.select();
         SWTBotMenu menuItem = launchTreeItem.contextMenu("Step Over"); 
         menuItem.click();
         TestSedCoreUtil.waitUntilDebugTargetCanSuspend(bot, target); // Wait until the target is resumed.
         assertFalse(leafStep.canStepOver());
         TestSedCoreUtil.waitUntilDebugTargetCanResume(bot, target); // wait until the target is suspended.
         assertTrue(leafStep.canStepOver());
      }
   }
   
   /**
    * Makes sure that a step return was done correctly.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step return on.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param expectedModelPathInBundle The path and file name of oracle file.
    * @param modelIndex The index of the oracle file.
    * @param expectedModelFileExtension The oracle file extension.
    * @throws DebugException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected void assertStepReturn(SWTWorkbenchBot bot, 
                                   SWTBotTreeItem launchTreeItem, 
                                   ISEDDebugTarget target,
                                   String expectedModelPathInBundle,
                                   int modelIndex,
                                   String expectedModelFileExtension) throws DebugException, IOException, ParserConfigurationException, SAXException {
      stepReturn(bot, launchTreeItem, target);
      assertStep(target, expectedModelPathInBundle, modelIndex, expectedModelFileExtension);
   }
   
   /**
    * Performs a step return on the given {@link SWTBotTreeItem}.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step return on.
    * @param target The {@link ISEDDebugTarget} to use.
    */
   protected static void stepReturn(SWTWorkbenchBot bot, 
                                    SWTBotTreeItem launchTreeItem, 
                                    ISEDDebugTarget target) {
      assertNotNull(bot);
      assertNotNull(launchTreeItem);
      assertNotNull(target);
      Object leafData = TestUtilsUtil.getTreeItemData(launchTreeItem);
      if (leafData instanceof IStep) {
         IStep leafStep = (IStep)leafData;
         assertTrue(leafStep.canStepReturn());
         launchTreeItem.select();
         SWTBotMenu menuItem = launchTreeItem.contextMenu("Step Return"); 
         menuItem.click();
         TestSedCoreUtil.waitUntilDebugTargetCanSuspend(bot, target); // Wait until the target is resumed.
         assertFalse(leafStep.canStepReturn());
         TestSedCoreUtil.waitUntilDebugTargetCanResume(bot, target); // wait until the target is suspended.
         assertTrue(leafStep.canStepReturn());
      }
   }
   
   /**
    * Makes sure that a resume was done correctly.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform resume on.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param expectedModelPathInBundle The path and file name of oracle file.
    * @param modelIndex The index of the oracle file.
    * @param expectedModelFileExtension The oracle file extension.
    * @throws DebugException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected void assertResume(SWTWorkbenchBot bot, 
                               SWTBotTreeItem launchTreeItem, 
                               ISEDDebugTarget target,
                               String expectedModelPathInBundle,
                               int modelIndex,
                               String expectedModelFileExtension) throws DebugException, IOException, ParserConfigurationException, SAXException {
      resume(bot, launchTreeItem, target);
      assertStep(target, expectedModelPathInBundle, modelIndex, expectedModelFileExtension);
   }
   
   /**
    * Performs a resume on the given {@link SWTBotTreeItem}.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform resume on.
    * @param target The {@link ISEDDebugTarget} to use.
    */
   protected static void resume(SWTWorkbenchBot bot, 
                                SWTBotTreeItem launchTreeItem, 
                                ISEDDebugTarget target) {
      assertNotNull(bot);
      assertNotNull(launchTreeItem);
      assertNotNull(target);
      Object leafData = TestUtilsUtil.getTreeItemData(launchTreeItem);
      if (leafData instanceof ISuspendResume) {
         ISuspendResume leafStep = (ISuspendResume)leafData;
         assertTrue(leafStep.canResume());
         launchTreeItem.select();
         SWTBotMenu menuItem = launchTreeItem.contextMenu("Resume"); 
         menuItem.click();
         TestSedCoreUtil.waitUntilDebugTargetCanSuspend(bot, target); // Wait until the target is resumed.
         assertFalse(leafStep.canResume());
         TestSedCoreUtil.waitUntilDebugTargetCanResume(bot, target); // wait until the target is suspended.
         assertTrue(leafStep.canResume());
      }
   }
   
   /**
    * Performs a test on a {@link KeYDebugTarget}. This methods setups
    * the environment an the real test is done in the given {@link IKeYDebugTargetTestExecutor}.
    * @param projectName The project name.
    * @param pathInBundle The path to the test files in bundle.
    * @param selector The {@link IMethodSelector} to select the {@link IMethod} to debug.
    * @param showMethodReturnValues Show method return values?
    * @param timeoutFactor The timeout factor used to increase {@link SWTBotPreferences#TIMEOUT}.
    * @param executor The {@link IKeYDebugTargetTestExecutor} which does the real test steps.
    * @throws Exception Occurred Exception.
    */
   protected void doKeYDebugTargetTest(String projectName,
                                       String pathInBundle,
                                       IMethodSelector selector,
                                       Boolean showMethodReturnValues,
                                       int timeoutFactor,
                                       IKeYDebugTargetTestExecutor executor) throws Exception {
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
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * timeoutFactor;
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
         TestSEDKeyCoreUtil.launchKeY(method, showMethodReturnValues);
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         ILaunch launch = target.getLaunch();
         // Do test
         executor.test(bot, project, method, targetName, debugView, debugTree, target, launch);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Restore runtime option
         if (originalRuntimeExceptions != null) {
            KeYUtil.setChoiceSetting(KeYUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalRuntimeExceptions);
         }
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         // Restore perspective
         defaultPerspective.activate();
      }
   }
   
   /**
    * Does a test in an environment configured via
    * {@link AbstractKeYDebugTargetTestCase#doKeYDebugTargetTest(String, String, IMethodSelector, boolean, int, IKeYDebugTargetTestExecutor)}.
    * @author Martin Hentschel
    */
   protected static interface IKeYDebugTargetTestExecutor {
      /**
       * Does the test.
       * @param bot The {@link SWTWorkbenchBot} to use.
       * @param project The {@link IJavaProject} which contains the source code.
       * @param method The {@link IMethod} which is debugged.
       * @param targetName The name of the launch configuration.
       * @param debugView The launch view.
       * @param debugTree The tree of the launch view.
       * @param target The created {@link ISEDDebugTarget}.
       * @param launch The {@link ILaunch} which is executed.
       * @throws Exception Occurred Exception.
       */
      public void test(SWTWorkbenchBot bot, 
                       IJavaProject project, 
                       IMethod method, 
                       String targetName, 
                       SWTBotView debugView, 
                       SWTBotTree debugTree, 
                       ISEDDebugTarget target, 
                       ILaunch launch) throws Exception;
   }
}
