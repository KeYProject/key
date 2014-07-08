/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.core.test.testcase.swtbot;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import javax.xml.parsers.ParserConfigurationException;

import org.eclipse.core.resources.IFile;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IStep;
import org.eclipse.debug.core.model.ISuspendResume;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Before;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.core.test.util.DebugTargetResumeSuspendListener;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.sed.key.core.test.util.TestSEDKeyCoreUtil;
import org.key_project.sed.key.ui.view.SymbolicExecutionSettingsView;
import org.key_project.sed.ui.visualization.view.ExecutionTreeThumbNailView;
import org.key_project.sed.ui.visualization.view.ExecutionTreeView;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;
import org.xml.sax.SAXException;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Provides the functionality to test {@link KeYDebugTarget}s.
 * @author Martin Hentschel
 */
public class AbstractKeYDebugTargetTestCase extends AbstractSetupTestCase {
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
    * @param saveCallStack Save call stack?
    * @throws IOException Occurred Exception.
    * @throws DebugException Occurred Exception.
    */
   protected static void createOracleFile(ISEDDebugTarget target, 
                                          String expectedModelPathInBundle, 
                                          boolean saveVariables,
                                          boolean saveCallStack) throws IOException, DebugException {
      if (oracleDirectory != null && oracleDirectory.isDirectory()) {
         createOracleFile(oracleDirectory, target, expectedModelPathInBundle, saveVariables, saveCallStack);
      }
   }

   
   /**
    * Creates a new oracle file for the given {@link ISEDDebugTarget}.
    * @param oracleDirectory The oracle directory to create file in.
    * @param target The given {@link ISEDDebugTarget} which provides the oracle data.
    * @param expectedModelPathInBundle The path in the bundle under that the created oracle file will be later available. It is used to create sub directories in temp directory.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @throws IOException Occurred Exception.
    * @throws DebugException Occurred Exception.
    */
   protected static void createOracleFile(File oracleDirectory,
                                          ISEDDebugTarget target, 
                                          String expectedModelPathInBundle, 
                                          boolean saveVariables,
                                          boolean saveCallStack) throws IOException, DebugException {
      // Create sub folder structure
      File oracleFile = new File(oracleDirectory, expectedModelPathInBundle);
      oracleFile.getParentFile().mkdirs();
      // Create oracle file
      SEDXMLWriter writer = new SEDXMLWriter();
      writer.write(target.getLaunch(), SEDXMLWriter.DEFAULT_ENCODING, new FileOutputStream(oracleFile), saveVariables, saveCallStack, null);
      // Print message to the user.
      printOracleDirectory();
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
    * @param bundleId The plug-in ID which contains the expected model path.
    * @param expectedModelPathInBundle The expected path to the oracle file.
    * @param includeVariables Include variables?
    * @param includeCallStack Include call stack?
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    */
   protected static void assertDebugTargetViaOracle(ISEDDebugTarget target,
                                                    String bundleId,
                                                    String expectedModelPathInBundle,
                                                    boolean includeVariables,
                                                    boolean includeCallStack) throws DebugException, IOException, ParserConfigurationException, SAXException {
      createOracleFile(target, expectedModelPathInBundle, includeVariables, includeCallStack);
      if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
         ISEDDebugTarget expectedDebugTarget = TestSEDKeyCoreUtil.createExpectedModel(bundleId, expectedModelPathInBundle);
         TestSedCoreUtil.compareDebugTarget(expectedDebugTarget, target, false, includeVariables, includeCallStack);
      }
   }
   
   
   /**
    * Makes sure that one test step is correctly done.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param bundleId The plug-in ID which contains the expected model path.
    * @param expectedModelPathInBundle The path and file name of oracle file.
    * @param modelIndex The index of the oracle file.
    * @param expectedModelFileExtension The oracle file extension.
    * @throws DebugException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected static void assertStep(ISEDDebugTarget target,
                                    String bundleId,
                                    String expectedModelPathInBundle,
                                    int modelIndex,
                                    String expectedModelFileExtension) throws DebugException, IOException, ParserConfigurationException, SAXException {
      assertDebugTargetViaOracle(target, bundleId, expectedModelPathInBundle + modelIndex + expectedModelFileExtension, false, false);
   }
   
   /**
    * Makes sure that a step into was done correctly.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step into on.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param bundleId The plug-in ID which contains the expected model path.
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
                                 String bundleId,
                                 String expectedModelPathInBundle,
                                 int modelIndex,
                                 String expectedModelFileExtension) throws DebugException, IOException, ParserConfigurationException, SAXException {
      stepInto(bot, launchTreeItem, target);
      assertStep(target, bundleId, expectedModelPathInBundle, modelIndex, expectedModelFileExtension);
   }
   
   /**
    * Performs a step into on the given {@link SWTBotTreeItem}.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step into on.
    * @param target The {@link ISEDDebugTarget} to use.
    */
   protected static void stepInto(SWTWorkbenchBot bot, 
                                  final SWTBotTreeItem launchTreeItem, 
                                  ISEDDebugTarget target) {
      assertNotNull(bot);
      assertNotNull(launchTreeItem);
      assertNotNull(target);
      Object leafData = TestUtilsUtil.getTreeItemData(launchTreeItem);
      if (leafData instanceof IStep) {
         IStep leafStep = (IStep)leafData;
         assertTrue(leafStep.canStepInto());
         launchTreeItem.select();
         // Click on "Step Into" and wait until step was executed.
         DebugTargetResumeSuspendListener.run(bot, target, new Runnable() {
            @Override
            public void run() {
               SWTBotMenu menuItem = launchTreeItem.contextMenu("Step Into"); 
               menuItem.click();
            }
         });
         waitUntilDeselected(bot, launchTreeItem);
      }
   }
   
   /**
    * Waits until the given {@link SWTBotTreeItem} is no longer selected.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param item The {@link SWTBotTreeItem} to wait for.
    */
   protected static void waitUntilDeselected(SWTWorkbenchBot bot, SWTBotTreeItem item) {
      TestUtilsUtil.waitUntilDeselected(bot, item);
   }
   
   /**
    * Makes sure that a step over was done correctly.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step over on.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param bundleId The plug-in ID which contains the expected model path.
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
                                 String bundleId,
                                 String expectedModelPathInBundle,
                                 int modelIndex,
                                 String expectedModelFileExtension) throws DebugException, IOException, ParserConfigurationException, SAXException {
      stepOver(bot, launchTreeItem, target);
      assertStep(target, bundleId, expectedModelPathInBundle, modelIndex, expectedModelFileExtension);
   }
   
   /**
    * Performs a step over on the given {@link SWTBotTreeItem}.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step over on.
    * @param target The {@link ISEDDebugTarget} to use.
    */
   protected static void stepOver(SWTWorkbenchBot bot, 
                                  final SWTBotTreeItem launchTreeItem, 
                                  ISEDDebugTarget target) {
      assertNotNull(bot);
      assertNotNull(launchTreeItem);
      assertNotNull(target);
      Object leafData = TestUtilsUtil.getTreeItemData(launchTreeItem);
      if (leafData instanceof IStep) {
         IStep leafStep = (IStep)leafData;
         assertTrue(leafStep.canStepOver());
         launchTreeItem.select();
         // Click on "Step Over" and wait until step was executed.
         DebugTargetResumeSuspendListener.run(bot, target, new Runnable() {
            @Override
            public void run() {
               SWTBotMenu menuItem = launchTreeItem.contextMenu("Step Over"); 
               menuItem.click();
            }
         });
         waitUntilDeselected(bot, launchTreeItem);
      }
   }
   
   /**
    * Makes sure that a step return was done correctly.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step return on.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param bundleId The plug-in ID which contains the expected model path.
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
                                   String bundleId,
                                   String expectedModelPathInBundle,
                                   int modelIndex,
                                   String expectedModelFileExtension) throws DebugException, IOException, ParserConfigurationException, SAXException {
      stepReturn(bot, launchTreeItem, target);
      assertStep(target, bundleId, expectedModelPathInBundle, modelIndex, expectedModelFileExtension);
   }
   
   /**
    * Performs a step return on the given {@link SWTBotTreeItem}.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform step return on.
    * @param target The {@link ISEDDebugTarget} to use.
    */
   protected static void stepReturn(SWTWorkbenchBot bot, 
                                    final SWTBotTreeItem launchTreeItem, 
                                    ISEDDebugTarget target) {
      assertNotNull(bot);
      assertNotNull(launchTreeItem);
      assertNotNull(target);
      Object leafData = TestUtilsUtil.getTreeItemData(launchTreeItem);
      if (leafData instanceof IStep) {
         IStep leafStep = (IStep)leafData;
         assertTrue(leafStep.canStepReturn());
         launchTreeItem.select();
         // Click on "Step Return" and wait until step was executed.
         DebugTargetResumeSuspendListener.run(bot, target, new Runnable() {
            @Override
            public void run() {
               SWTBotMenu menuItem = launchTreeItem.contextMenu("Step Return"); 
               menuItem.click();
            }
         });
         waitUntilDeselected(bot, launchTreeItem);
      }
   }
   
   /**
    * Makes sure that a resume was done correctly.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform resume on.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param bundleId The plug-in ID which contains the expected model path.
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
                               String bundleId,
                               String expectedModelPathInBundle,
                               int modelIndex,
                               String expectedModelFileExtension) throws DebugException, IOException, ParserConfigurationException, SAXException {
      resume(bot, launchTreeItem, target);
      assertStep(target, bundleId, expectedModelPathInBundle, modelIndex, expectedModelFileExtension);
   }
   
   /**
    * Performs a resume on the given {@link SWTBotTreeItem}.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param launchTreeItem The {@link SWTBotTreeItem} to perform resume on.
    * @param target The {@link ISEDDebugTarget} to use.
    */
   protected static void resume(SWTWorkbenchBot bot, 
                                final SWTBotTreeItem launchTreeItem, 
                                ISEDDebugTarget target) {
      assertNotNull(bot);
      assertNotNull(launchTreeItem);
      assertNotNull(target);
      Object leafData = TestUtilsUtil.getTreeItemData(launchTreeItem);
      if (leafData instanceof ISuspendResume) {
         ISuspendResume leafStep = (ISuspendResume)leafData;
         assertTrue(leafStep.canResume());
         launchTreeItem.select();
         // Click on "Resume" and wait until step was executed.
         DebugTargetResumeSuspendListener.run(bot, target, new Runnable() {
            @Override
            public void run() {
               SWTBotMenu menuItem = launchTreeItem.contextMenu("Resume"); 
               menuItem.click();
            }
         });
      }
   }
   
   /**
    * Performs a test on a {@link KeYDebugTarget}. This methods setups
    * the environment an the real test is done in the given {@link IKeYDebugTargetTestExecutor}.
    * @param projectName The project name.
    * @param pathInBundle The path to the test files in bundle.
    * @param closePropertiesView Close properties sheet page?
    * @param closeExecutionTreeViews Close the views which visualizes the symbolic execution tree? Will increase the test perforamnce.
    * @param selector The {@link IMethodSelector} to select the {@link IMethod} to debug.
    * @param useExistingContract Use existing contract? Use {@code null} to use default value.
    * @param preconditionOrExistingContract Optional precondition or the ID of the existing contract to use Use {@code null} to use default value.
    * @param showMethodReturnValues Show method return values?
    * @param showVariablesOfSelectedDebugNode Show variables of selected debug node?
    * @param showKeYMainWindow Show KeY's main window?
    * @param mergeBranchConditions Merge branch conditions?
    * @param useUnicode Use unicode characters?
    * @param usePrettyPrinting Use pretty printing?
    * @param showSignatureOnMethodReturnNodes Show signature on method return nodes?
    * @param timeoutFactor The timeout factor used to increase {@link SWTBotPreferences#TIMEOUT}.
    * @param executor The {@link IKeYDebugTargetTestExecutor} which does the real test steps.
    * @throws Exception Occurred Exception.
    */
   protected void doKeYDebugTargetTest(String projectName,
                                       String pathInBundle,
                                       boolean closePropertiesView,
                                       boolean closeExecutionTreeViews,
                                       IMethodSelector selector,
                                       Boolean useExistingContract,
                                       String preconditionOrExistingContract,
                                       Boolean showMethodReturnValues,
                                       Boolean showVariablesOfSelectedDebugNode,
                                       Boolean showKeYMainWindow,
                                       Boolean mergeBranchConditions,
                                       Boolean useUnicode,
                                       Boolean usePrettyPrinting,
                                       Boolean showSignatureOnMethodReturnNodes,
                                       int timeoutFactor, 
                                       IKeYDebugTargetTestExecutor executor) throws Exception {
      doKeYDebugTargetTest(projectName,
                           Activator.PLUGIN_ID, 
                           pathInBundle, 
                           closePropertiesView,
                           closeExecutionTreeViews, 
                           selector, 
                           useExistingContract,
                           preconditionOrExistingContract,
                           showMethodReturnValues, 
                           showVariablesOfSelectedDebugNode, 
                           showKeYMainWindow, 
                           mergeBranchConditions,
                           useUnicode,
                           usePrettyPrinting,
                           showSignatureOnMethodReturnNodes,
                           timeoutFactor, 
                           executor);
   }


   /**
    * Performs a test on a {@link KeYDebugTarget}. This methods setups
    * the environment an the real test is done in the given {@link IKeYDebugTargetTestExecutor}.
    * @param projectName The project name.
    * @param plugin The plug-in which contains the test data.
    * @param pathInBundle The path to the test files in bundle.
    * @param closePropertiesView Close properties sheet page?
    * @param closeExecutionTreeViews Close the views which visualizes the symbolic execution tree? Will increase the test perforamnce.
    * @param selector The {@link IMethodSelector} to select the {@link IMethod} to debug.
    * @param useExistingContract Use existing contract? Use {@code null} to use default value.
    * @param preconditionOrExistingContract Optional precondition or the ID of the existing contract to use Use {@code null} to use default value.
    * @param showMethodReturnValues Show method return values?
    * @param showVariablesOfSelectedDebugNode Show variables of selected debug node?
    * @param showKeYMainWindow Show KeY's main window?
    * @param mergeBranchConditions Merge branch conditions?
    * @param useUnicode Use unicode characters?
    * @param usePrettyPrinting Use pretty printing?
    * @param showSignatureOnMethodReturnNodes Show signature on method return nodes?
    * @param timeoutFactor The timeout factor used to increase {@link SWTBotPreferences#TIMEOUT}.
    * @param executor The {@link IKeYDebugTargetTestExecutor} which does the real test steps.
    * @throws Exception Occurred Exception.
    */
   protected void doKeYDebugTargetTest(String projectName,
                                       String plugin,
                                       String pathInBundle,
                                       boolean closePropertiesView,
                                       boolean closeExecutionTreeViews,
                                       IMethodSelector selector,
                                       Boolean useExistingContract,
                                       String preconditionOrExistingContract,
                                       Boolean showMethodReturnValues,
                                       Boolean showVariablesOfSelectedDebugNode,
                                       Boolean showKeYMainWindow,
                                       Boolean mergeBranchConditions,
                                       Boolean useUnicode,
                                       Boolean usePrettyPrinting,
                                       Boolean showSignatureOnMethodReturnNodes,
                                       int timeoutFactor,
                                       IKeYDebugTargetTestExecutor executor) throws Exception {
      doKeYDebugTargetTest(projectName, 
                           plugin, 
                           pathInBundle, 
                           null, 
                           closePropertiesView, 
                           closeExecutionTreeViews, 
                           selector, 
                           useExistingContract, 
                           preconditionOrExistingContract, 
                           showMethodReturnValues, 
                           showVariablesOfSelectedDebugNode, 
                           showKeYMainWindow, 
                           mergeBranchConditions, 
                           useUnicode,
                           usePrettyPrinting,
                           showSignatureOnMethodReturnNodes,
                           timeoutFactor, 
                           executor);
   }
   
   /**
    * Performs a test on a {@link KeYDebugTarget}. This methods setups
    * the environment an the real test is done in the given {@link IKeYDebugTargetTestExecutor}.
    * @param projectName The project name.
    * @param plugin The plug-in which contains the test data.
    * @param pathInBundle The path to the test files in bundle.
    * @param projectConfigurator An optional {@link IProjectConfigurator}.
    * @param closePropertiesView Close properties sheet page?
    * @param closeExecutionTreeViews Close the views which visualizes the symbolic execution tree? Will increase the test perforamnce.
    * @param selector The {@link IMethodSelector} to select the {@link IMethod} to debug.
    * @param useExistingContract Use existing contract? Use {@code null} to use default value.
    * @param preconditionOrExistingContract Optional precondition or the ID of the existing contract to use Use {@code null} to use default value.
    * @param showMethodReturnValues Show method return values?
    * @param showVariablesOfSelectedDebugNode Show variables of selected debug node?
    * @param showKeYMainWindow Show KeY's main window?
    * @param mergeBranchConditions Merge branch conditions?
    * @param useUnicode Use unicode characters?
    * @param usePrettyPrinting Use pretty printing?
    * @param showSignatureOnMethodReturnNodes Show signature on method return nodes?
    * @param timeoutFactor The timeout factor used to increase {@link SWTBotPreferences#TIMEOUT}.
    * @param executor The {@link IKeYDebugTargetTestExecutor} which does the real test steps.
    * @throws Exception Occurred Exception.
    */
   protected void doKeYDebugTargetTest(String projectName,
                                       String plugin,
                                       String pathInBundle,
                                       IProjectConfigurator projectConfigurator,
                                       boolean closePropertiesView,
                                       boolean closeExecutionTreeViews,
                                       IMethodSelector selector,
                                       Boolean useExistingContract,
                                       String preconditionOrExistingContract,
                                       Boolean showMethodReturnValues,
                                       Boolean showVariablesOfSelectedDebugNode,
                                       Boolean showKeYMainWindow,
                                       Boolean mergeBranchConditions,
                                       Boolean useUnicode,
                                       Boolean usePrettyPrinting,
                                       Boolean showSignatureOnMethodReturnNodes,
                                       int timeoutFactor,
                                       IKeYDebugTargetTestExecutor executor) throws Exception {
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
      BundleUtil.extractFromBundleToWorkspace(plugin, pathInBundle, project.getProject().getFolder("src"));
      if (projectConfigurator != null) {
         projectConfigurator.configure(project);
      }
      // Do test steps
      doKeYDebugTargetTest(project, closePropertiesView, closeExecutionTreeViews, selector, useExistingContract, preconditionOrExistingContract, showMethodReturnValues, showVariablesOfSelectedDebugNode, showKeYMainWindow, mergeBranchConditions, useUnicode, usePrettyPrinting, showSignatureOnMethodReturnNodes, timeoutFactor, executor);
   }
   
   /**
    * Performs a test on a {@link KeYDebugTarget}. This methods setups
    * the environment an the real test is done in the given {@link IKeYDebugTargetTestExecutor}.
    * @param project The {@link IJavaProject} which provides the content.
    * @param closePropertiesView Close properties sheet page?
    * @param closeExecutionTreeViews Close the views which visualizes the symbolic execution tree? Will increase the test perforamnce.
    * @param selector The {@link IMethodSelector} to select the {@link IMethod} to debug.
    * @param useExistingContract Use existing contract? Use {@code null} to use default value.
    * @param preconditionOrExistingContract Optional precondition or the ID of the existing contract to use Use {@code null} to use default value.
    * @param showMethodReturnValues Show method return values?
    * @param showVariablesOfSelectedDebugNode Show variables of selected debug node?
    * @param showKeYMainWindow Show KeY's main window?
    * @param mergeBranchConditions Merge branch conditions?
    * @param useUnicode Use unicode characters?
    * @param usePrettyPrinting Use pretty printing?
    * @param showSignatureOnMethodReturnNodes Show signature on method return nodes?
    * @param timeoutFactor The timeout factor used to increase {@link SWTBotPreferences#TIMEOUT}.
    * @param executor The {@link IKeYDebugTargetTestExecutor} which does the real test steps.
    * @throws Exception Occurred Exception.
    */
   protected void doKeYDebugTargetTest(IJavaProject project,
                                       boolean closePropertiesView,
                                       boolean closeExecutionTreeViews,
                                       IMethodSelector selector,
                                       Boolean useExistingContract,
                                       String preconditionOrExistingContract,
                                       Boolean showMethodReturnValues,
                                       Boolean showVariablesOfSelectedDebugNode,
                                       Boolean showKeYMainWindow,
                                       Boolean mergeBranchConditions,
                                       Boolean useUnicode,
                                       Boolean usePrettyPrinting,
                                       Boolean showSignatureOnMethodReturnNodes,
                                       int timeoutFactor,
                                       IKeYDebugTargetTestExecutor executor) throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      boolean restoreExecutionTreeView = false;
      boolean restoreThumbinalExecutionTreeView = false;
      boolean restorePropertiesView = false;
      List<? extends SWTBotEditor> oldEditors = bot.editors();
      // Open symbolic debug perspective
      IPerspectiveDescriptor debugPerspective = TestSedCoreUtil.openSymbolicDebugPerspective();
      try {
         // Configure debug perspective
         if (closeExecutionTreeViews) {
            restoreExecutionTreeView = TestUtilsUtil.closeView(ExecutionTreeView.VIEW_ID);
            restoreThumbinalExecutionTreeView = TestUtilsUtil.closeView(ExecutionTreeThumbNailView.VIEW_ID);
         }
         if (closePropertiesView) {
            restorePropertiesView = TestUtilsUtil.closeView(IPageLayout.ID_PROP_SHEET);
         }
         executor.configureDebugPerspective(bot, debugPerspective);
         // Get method
         assertNotNull(selector);
         IMethod method = selector.getMethod(project);
         String targetName = useExistingContract != null && useExistingContract.booleanValue() ? 
                             preconditionOrExistingContract : 
                             TestSEDKeyCoreUtil.computeTargetName(method);
         // Increase timeout
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * timeoutFactor;
         // Set choice settings in KeY.
         SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW);
         assertEquals(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW, SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS));
         // Launch method
         TestSEDKeyCoreUtil.launchKeY(method, useExistingContract, preconditionOrExistingContract, showMethodReturnValues, showVariablesOfSelectedDebugNode, showKeYMainWindow, mergeBranchConditions, useUnicode, usePrettyPrinting, showSignatureOnMethodReturnNodes);
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
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         // Make sure that all jobs are done because otherwise older jobs may influence the next test execution
         TestUtilsUtil.waitForJobs();
         // Close all opened editors which where not opened before test execution
         List<? extends SWTBotEditor> currentEditors = bot.editors();
         for (SWTBotEditor editor : currentEditors) {
            if (!oldEditors.contains(editor)) {
               editor.close();
            }
         }
         // Restore closed views if required
         executor.cleanupDebugPerspective(bot, debugPerspective);
         if (restorePropertiesView) {
            TestUtilsUtil.openView(IPageLayout.ID_PROP_SHEET);
         }
         if (restoreExecutionTreeView) {
            TestUtilsUtil.openView(ExecutionTreeView.VIEW_ID);
         }
         if (restoreThumbinalExecutionTreeView) {
            TestUtilsUtil.openView(ExecutionTreeThumbNailView.VIEW_ID);
         }
         // Restore perspective
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }
   
   protected IKeYDebugTargetTestExecutor createResumeExecutor(final boolean clearProofListInKeYBeforeResume,
                                                              final String bundleId,
                                                              final String expectedModelPathInBundle,
                                                              final boolean includeVariables,
                                                              final boolean includeCallstack,
                                                              final boolean stepIntoInsteadOfRun,
                                                              final boolean mergeBranchConditions,
                                                              final boolean useMethodContracts,
                                                              final boolean useLoopInvariants,
                                                              final boolean nonExecutionBranchHidingSideProofs,
                                                              final boolean aliasChecks) {
      return new AbstractKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
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
            // Configure operation contract and loop invariant usage
            SWTBotView symbolicSettingsView = bot.viewById(SymbolicExecutionSettingsView.VIEW_ID);
            if (useMethodContracts) {
               TestUtilsUtil.clickDirectly(symbolicSettingsView.bot().radio(SymbolicExecutionStrategy.Factory.METHOD_TREATMENT_CONTRACT));
            }
            else {
               TestUtilsUtil.clickDirectly(symbolicSettingsView.bot().radio(SymbolicExecutionStrategy.Factory.METHOD_TREATMENT_EXPAND, 0));
            }
            if (useLoopInvariants) {
               TestUtilsUtil.clickDirectly(symbolicSettingsView.bot().radio(SymbolicExecutionStrategy.Factory.LOOP_TREATMENT_INVARIANT));
            }
            else {
               TestUtilsUtil.clickDirectly(symbolicSettingsView.bot().radio(SymbolicExecutionStrategy.Factory.LOOP_TREATMENT_EXPAND, 1));
            }
            if (nonExecutionBranchHidingSideProofs) {
               TestUtilsUtil.clickDirectly(symbolicSettingsView.bot().radio(SymbolicExecutionStrategy.Factory.NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF));
            }
            else {
               TestUtilsUtil.clickDirectly(symbolicSettingsView.bot().radio(SymbolicExecutionStrategy.Factory.NON_EXECUTION_BRANCH_HIDING_OFF));
            }
            if (aliasChecks) {
               TestUtilsUtil.clickDirectly(symbolicSettingsView.bot().radio(SymbolicExecutionStrategy.Factory.ALIAS_CHECK_IMMEDIATELY));
            }
            else {
               TestUtilsUtil.clickDirectly(symbolicSettingsView.bot().radio(SymbolicExecutionStrategy.Factory.ALIAS_CHECK_NEVER));
            }
            // Get debug target TreeItem
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0); // Select first debug target
            // Create tree
            if (stepIntoInsteadOfRun) {
               // Step into on each SET node
               Set<Object> stepDone = new HashSet<Object>();
               boolean newStepDone = true;
               do {
                  newStepDone = false;
                  List<SWTBotTreeItem> leafItems = TestUtilsUtil.collectLeafs(item);
                  for (SWTBotTreeItem leafItem : leafItems) {
                     Object leafData = TestUtilsUtil.getTreeItemData(leafItem);
                     if (stepDone.add(leafData)) {
                        newStepDone = true;
                        stepInto(bot, leafItem, target);
                     }
                  }
               } while (newStepDone);
            }
            else {
               // Find resume menu item; must be done before proof is removed.
               SWTBotMenu menuItem = item.contextMenu("Resume");
               // Remove proof in KeY if required
               if (clearProofListInKeYBeforeResume) {
                  assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
                  KeYUtil.clearProofList(MainWindow.getInstance());
                  assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
               }
               // Resume
               menuItem.click();
            }
            // Evaluate created tree
            if (clearProofListInKeYBeforeResume) {
               assertTrue(launch.canTerminate());
               assertTrue(launch.isTerminated()); // launch.isTerminated() returns true if terminated or disconnected.
               assertFalse(target.canDisconnect());
               assertFalse(target.canSuspend());
               assertTrue(target.canTerminate());
               assertTrue(target.isDisconnected());
               assertTrue(target.isSuspended());
               assertFalse(target.isTerminated());
               assertFalse(target.canResume());
               // Test the execution tree
               TestSEDKeyCoreUtil.assertInitialTarget(target, targetName);
            }
            else {
               if (!stepIntoInsteadOfRun) {
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
               }
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
               assertDebugTargetViaOracle(target, bundleId, expectedModelPathInBundle, includeVariables, includeCallstack);
            }
         }
      };
   }
   
   /**
    * Instances of this class can be used to configure an {@link IJavaProject}.
    * @author Martin Hentschel
    */
   protected static interface IProjectConfigurator {
      /**
       * Configures the given {@link IJavaProject}.
       * @param javaProject The {@link IJavaProject} to configure.
       */
      public void configure(IJavaProject javaProject) throws Exception;
   }
   
   /**
    * Does a test in an environment configured via
    * {@link AbstractKeYDebugTargetTestCase#doKeYDebugTargetTest(String, String, IMethodSelector, boolean, int, IKeYDebugTargetTestExecutor)}.
    * @author Martin Hentschel
    */
   protected static interface IKeYDebugTargetTestExecutor {
      /**
       * Can be used to initialize the debug perspective.
       * @param bot The {@link SWTWorkbenchBot} to use.
       * @param debugPerspective The currently shown debug perspective.
       * @throws Exception Occurred Exception.
       */
      public void configureDebugPerspective(SWTWorkbenchBot bot, 
                                            IPerspectiveDescriptor debugPerspective) throws Exception;
      
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
      
      /**
       * Reverts all changes done on the debug perspective.
       * @param bot The {@link SWTWorkbenchBot} to use.
       * @param debugPerspective The currently shown debug perspective.
       * @throws Exception Occurred Exception.
       */
      public void cleanupDebugPerspective(SWTWorkbenchBot bot, 
                                          IPerspectiveDescriptor debugPerspective) throws Exception;
   }

   /**
    * Abstract implementation of {@link IKeYDebugTargetTestExecutor} which does nothing.
    * @author Martin Hentschel
    */
   protected static abstract class AbstractKeYDebugTargetTestExecutor implements IKeYDebugTargetTestExecutor {
      /**
       * {@inheritDoc}
       */
      @Override
      public void configureDebugPerspective(SWTWorkbenchBot bot, IPerspectiveDescriptor debugPerspective) throws Exception {
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void cleanupDebugPerspective(SWTWorkbenchBot bot, IPerspectiveDescriptor debugPerspective) throws Exception {
      }
   }
   
   /**
    * Performs a test on a {@link KeYDebugTarget}. This methods setups
    * the environment an the real test is done in the given {@link IKeYDebugTargetTestExecutor}.
    * @param projectName The project name.
    * @param plugin The plug-in which contains the test data.
    * @param pathInBundle The path to the test files in bundle.
    * @param closePropertiesView Close properties sheet page?
    * @param closeExecutionTreeViews Close the views which visualizes the symbolic execution tree? Will increase the test perforamnce.
    * @param selector The {@link IFileSelector} to select the {@link IFIle} to debug.
    * @param showMethodReturnValues Show method return values?
    * @param showVariablesOfSelectedDebugNode Show variables of selected debug node?
    * @param showKeYMainWindow Show KeY's main window?
    * @param mergeBranchConditions Merge branch conditions?
    * @param usePrettyPrinting Use pretty printing?
    * @param timeoutFactor The timeout factor used to increase {@link SWTBotPreferences#TIMEOUT}.
    * @param executor The {@link IKeYDebugTargetProofFileTestExecutor} which does the real test steps.
    * @throws Exception Occurred Exception.
    */
   protected void doKeYDebugTargetTest(String projectName,
                                       String plugin,
                                       String pathInBundle,
                                       boolean closePropertiesView,
                                       boolean closeExecutionTreeViews,
                                       IFileSelector selector,
                                       Boolean showMethodReturnValues,
                                       Boolean showVariablesOfSelectedDebugNode,
                                       Boolean showKeYMainWindow,
                                       Boolean mergeBranchConditions,
                                       Boolean usePrettyPrinting,
                                       int timeoutFactor,
                                       IKeYDebugTargetProofFileTestExecutor executor) throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      boolean restoreExecutionTreeView = false;
      boolean restoreThumbinalExecutionTreeView = false;
      boolean restorePropertiesView = false;
      List<? extends SWTBotEditor> oldEditors = bot.editors();
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
         if (closeExecutionTreeViews) {
            restoreExecutionTreeView = TestUtilsUtil.closeView(ExecutionTreeView.VIEW_ID);
            restoreThumbinalExecutionTreeView = TestUtilsUtil.closeView(ExecutionTreeThumbNailView.VIEW_ID);
         }
         if (closePropertiesView) {
            restorePropertiesView = TestUtilsUtil.closeView(IPageLayout.ID_PROP_SHEET);
         }
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
         BundleUtil.extractFromBundleToWorkspace(plugin, pathInBundle, project.getProject().getFolder("src"));
         // Get method
         assertNotNull(selector);
         IFile file = selector.getFile(project);
         String targetName = TestSEDKeyCoreUtil.computeTargetName(file);
         // Increase timeout
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * timeoutFactor;
         // Launch method
         TestSEDKeyCoreUtil.launchKeY(file, showMethodReturnValues, showVariablesOfSelectedDebugNode, showKeYMainWindow, mergeBranchConditions, usePrettyPrinting);
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         ILaunch launch = target.getLaunch();
         // Do test
         executor.test(bot, project, file, targetName, debugView, debugTree, target, launch);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         // Make sure that all jobs are done because otherwise older jobs may influence the next test execution
         TestUtilsUtil.waitForJobs();
         // Close all opened editors which where not opened before test execution
         List<? extends SWTBotEditor> currentEditors = bot.editors();
         for (SWTBotEditor editor : currentEditors) {
            if (!oldEditors.contains(editor)) {
               editor.close();
            }
         }
         // Restore closed views if required
         if (restorePropertiesView) {
            TestUtilsUtil.openView(IPageLayout.ID_PROP_SHEET);
         }
         if (restoreExecutionTreeView) {
            TestUtilsUtil.openView(ExecutionTreeView.VIEW_ID);
         }
         if (restoreThumbinalExecutionTreeView) {
            TestUtilsUtil.openView(ExecutionTreeThumbNailView.VIEW_ID);
         }
         // Restore perspective
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }
   
   /**
    * Utility class to select an {@link IFile} in a given {@link IJavaProject}.
    * @author Martin Hentschel
    */
   public static interface IFileSelector {
      /**
       * Selects an {@link IFile} in the given {@link IJavaProject}.
       * @param project The {@link IJavaProject}.
       * @return The selected {@link IFile}.
       * @throws Exception Occurred Exceptions.
       */
      public IFile getFile(IJavaProject project) throws Exception;
   }
   
   /**
    * Does a test in an environment configured via
    * {@link AbstractKeYDebugTargetTestCase#doKeYDebugTargetTest(String, String, String, boolean, boolean, IFileSelector, Boolean, Boolean, Boolean, Boolean, int, IKeYDebugTargetProofFileTestExecutor)}.
    * @author Martin Hentschel
    */
   protected static interface IKeYDebugTargetProofFileTestExecutor {
      /**
       * Does the test.
       * @param bot The {@link SWTWorkbenchBot} to use.
       * @param project The {@link IJavaProject} which contains the source code.
       * @param file The {@link IFile} which is debugged.
       * @param targetName The name of the launch configuration.
       * @param debugView The launch view.
       * @param debugTree The tree of the launch view.
       * @param target The created {@link ISEDDebugTarget}.
       * @param launch The {@link ILaunch} which is executed.
       * @throws Exception Occurred Exception.
       */
      public void test(SWTWorkbenchBot bot, 
                       IJavaProject project, 
                       IFile file, 
                       String targetName, 
                       SWTBotView debugView, 
                       SWTBotTree debugTree, 
                       ISEDDebugTarget target, 
                       ILaunch launch) throws Exception;
   }
}