package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.waits.Conditions;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.test.Activator;
import org.key_project.sed.ui.visualization.view.ExecutionTreeView;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides the basic functionality to test the visualization of symbolic execution trees.
 * @author Martin Hentschel
 */
public abstract class AbstractSymbolicExecutionTreeTest extends AbstractSWTBotSetFileTest {
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
    * Performs a layout test.
    * @param projectName The project Name.
    * @param pathInBundle The path in the bundle to the SET file.
    * @param pathToSetFile The path to the SET file in the created project.
    * @param pathToOracleFiles The path to the oracle files.
    * @param pathReplacements The path replacements to do.
    * @throws Exception Occurred Exception.
    */
   protected void doLayoutTest(final String projectName, 
                               String pathInBundle,
                               final String pathToSetFile,
                               final String pathToOracleFiles,
                               PathReplacement... pathReplacements) throws Exception {
      IDiagramTestSteps steps = new AbstractDiagramTestSteps() {
         @Override
         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            assertDiagram(bot, project, pathToSetFile, pathToOracleFiles, null);
         }
      };
      doDiagramTest(projectName, pathInBundle, pathToSetFile, steps, pathReplacements);
   }
   
   /**
    * Performs a diagram test.
    * @param projectName The project Name.
    * @param pathInBundle The path in the bundle to the SET file.
    * @param pathToSetFile The path to the SET file in the created project.
    * @param testSteps The {@link IDiagramTestSteps} to execute.
    * @param pathReplacements The path replacements to do.
    * @throws Exception Occurred Exception.
    */
   protected void doDiagramTest(final String projectName, 
                                String pathInBundle,
                                final String pathToSetFile,
                                final IDiagramTestSteps testSteps,
                                PathReplacement... pathReplacements) throws Exception {
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      try {
         // Close symbolic execution tree view to ensure that IDs start at 0 when diagram is visualized
         TestUtilsUtil.openPerspective(TestUtilsUtil.getPerspective(SymbolicDebugPerspectiveFactory.PERSPECTIVE_ID));
         TestUtilsUtil.closeView(ExecutionTreeView.VIEW_ID);
         TestUtilsUtil.openPerspective(originalPerspective);
         // Create diagram
         ISetFileTestSteps additionalTestSteps = new ISetFileTestSteps() {
            @Override
            public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               try {
                  testSteps.init(bot, project, setFile, debugView, debugTree, launch, target);
                  // Select debug target
                  TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0);
                  // Wait until diagram is completely constructed
                  TestUtilsUtil.openView(ExecutionTreeView.VIEW_ID);
                  TestUtilsUtil.waitForJobs();
                  // Perform test steps
                  testSteps.test(bot, project, setFile, debugView, debugTree, launch, target);
               }
               finally {
                  bot.closeAllEditors();
               }
            }
         };
         doSetFileTest(projectName, pathInBundle, pathToSetFile, additionalTestSteps, pathReplacements);
      }
      finally {
         TestUtilsUtil.openPerspective(originalPerspective);
      }
   }

   /**
    * Performs the test steps to test a shown {@link Diagram}.
    * @author Martin Hentschel
    */
   public static interface IDiagramTestSteps {
      /**
       * Performs some optional initializations before the set is visualized.
       * @param bot The used {@link SWTWorkbenchBot}.
       * @param project The {@link IProject} which contains the SET file.
       * @param setFile The SET file.
       * @param debugView The debug view.
       * @param debugTree The debug tree.
       * @param launch The {@link ILaunch}.
       * @param target The {@link ISEDDebugTarget}.
       */
      public void init(SWTWorkbenchBot bot, 
                       IProject project, 
                       IFile setFile, 
                       SWTBotView debugView, 
                       SWTBotTree debugTree, 
                       ILaunch launch, 
                       ISEDDebugTarget target) throws Exception;
      
      /**
       * Executes the test steps.
       * @param bot The used {@link SWTWorkbenchBot}.
       * @param project The {@link IProject} which contains the SET file.
       * @param setFile The SET file.
       * @param debugView The debug view.
       * @param debugTree The debug tree.
       * @param launch The {@link ILaunch}.
       * @param target The {@link ISEDDebugTarget}.
       */
      public void test(SWTWorkbenchBot bot, 
                       IProject project, 
                       IFile setFile, 
                       SWTBotView debugView, 
                       SWTBotTree debugTree, 
                       ILaunch launch, 
                       ISEDDebugTarget target) throws Exception;
   }

   /**
    * Provides some default implementations of {@link IDiagramTestSteps}.
    * @author Martin Hentschel
    */
   public static abstract class AbstractDiagramTestSteps implements IDiagramTestSteps {
      /**
       * {@inheritDoc}
       */
      @Override
      public void init(SWTWorkbenchBot bot, 
                       IProject project, 
                       IFile setFile, 
                       SWTBotView debugView, 
                       SWTBotTree debugTree, 
                       ILaunch launch, 
                       ISEDDebugTarget target) throws Exception {
      }
   }

   /**
    * Ensures that the current diagram matches the oracle files.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param project The {@link IProject} to which the diagram will be saved to.
    * @param pathToSetFile The path to the SET file in the created project.
    * @param pathToOracleFiles The path to the oracle files.
    * @param fileNameSuffix A file name suffix.
    * @throws Exception Occurred Exception
    */
   protected static void assertDiagram(SWTWorkbenchBot bot, 
                                       IProject project,
                                       String pathToSetFile,
                                       String pathToOracleFiles,
                                       String fileNameSuffix) throws Exception {
      // Open Save diagram wizard
      SWTBotView executionTreeView = bot.viewById(ExecutionTreeView.VIEW_ID);
      executionTreeView.setFocus();
      executionTreeView.toolbarButton("Save As").click();
      // Finish wizard
      SWTBotShell wizardShell = bot.shell("Save Symbolic Execution Tree Diagram");
      wizardShell.bot().tree().select(project.getName());
      final String fileName = "Current" + 
                              IOUtil.getFileNameWithoutExtension(pathToSetFile) +
                              (fileNameSuffix != null ? fileNameSuffix : "");
      wizardShell.bot().text(1).setText(fileName);
      TestUtilsUtil.clickDirectly(wizardShell.bot().button("Next >"));
      TestUtilsUtil.clickDirectly(wizardShell.bot().button("Finish"));
      bot.waitUntil(Conditions.shellCloses(wizardShell));
      if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
         // Save oracle file
         copyOracleFiles(pathToOracleFiles, project, fileName);
      }
      else {
         // Read diagram file
         String expectedDiagramFile = IOUtil.readFrom(BundleUtil.openInputStream(Activator.PLUGIN_ID, pathToOracleFiles + "/" + fileName + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT));
         String currentDiagramFile = ResourceUtil.readFrom(project.getFile(fileName + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT));
         // Update model path
         final String PROP_START = "<properties key=\"domainModelFile\" value=\"";
         int expectedStart = expectedDiagramFile.indexOf(PROP_START);
         int expectedEnd = expectedDiagramFile.indexOf("\"/>", expectedStart + PROP_START.length());
         int currentStart = currentDiagramFile.indexOf(PROP_START);
         int currentEnd = currentDiagramFile.indexOf("\"/>", currentStart + PROP_START.length());
         expectedDiagramFile = expectedDiagramFile.substring(0, expectedStart + PROP_START.length()) +
                               currentDiagramFile.substring(currentStart + PROP_START.length(), currentEnd) +
                               expectedDiagramFile.substring(expectedEnd);
         // Compare diagram files
         if (!StringUtil.equalIgnoreWhiteSpace(expectedDiagramFile, currentDiagramFile)) {
            assertEquals(expectedDiagramFile, currentDiagramFile); // Let test fail to have an improved comparison dialog
         }
      }
   }
   
   /**
    * Copies the oracle files into a temporary directory.
    * @param pathToOracleFiles The path to the oracle files.
    * @param project The {@link IProject} which contains the saved diagram.
    * @param fileName The file name of model and diagram file.
    * @throws CoreException Occurred Exception.
    */
   protected static void copyOracleFiles(String pathToOracleFiles,
                                         IProject project,
                                         String fileName) throws CoreException {
      // Create sub folder structure
      File targetOracleDirectory = new File(oracleDirectory, pathToOracleFiles);
      targetOracleDirectory.mkdirs();
      // Create oracle file
      ResourceUtil.copyIntoFileSystem(project.getFile(fileName + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT),
                                      new File(targetOracleDirectory, fileName + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT));
      ResourceUtil.copyIntoFileSystem(project.getFile(fileName + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT),
                                      new File(targetOracleDirectory, fileName + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT));
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
}
