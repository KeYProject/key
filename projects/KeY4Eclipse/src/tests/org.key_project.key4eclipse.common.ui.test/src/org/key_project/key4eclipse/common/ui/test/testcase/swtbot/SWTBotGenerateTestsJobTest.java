package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.waits.Conditions;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorReference;
import org.hamcrest.Matchers;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.key4eclipse.common.ui.testGeneration.EclipseTestGenerator;
import org.key_project.key4eclipse.common.ui.testGeneration.GenerateTestsJob;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.test.TestZ3;
import de.uka.ilkd.key.smt.testgen.AbstractTestGenerator;
import de.uka.ilkd.key.testgen.TestCaseGenerator;

/**
 * SWTBot tests for {@link GenerateTestsJob}.
 * 
 * The Z3 solver path ({@code z3SolverPath}) needs to be set, e.g. 
 * {@code -Dz3SolverPath=D:\Forschung\Tools\z3-4.3.0-x64\bin\z3.exe}
 * @author Martin Hentschel
 */
public class SWTBotGenerateTestsJobTest extends TestCase {
   /**
    * Tests the test generation with the magic42 example.
    */
   @Test
   public void testTestGeneration() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         bot.closeAllEditors();
         // Ensure that test generation is possible
         SolverType type = SolverType.Z3_CE_SOLVER;
         String solverPathProperty = System.getProperty(TestZ3.SYSTEM_PROPERTY_SOLVER_PATH);
         if (!StringUtil.isTrimmedEmpty(solverPathProperty)) {
            type.setSolverCommand(solverPathProperty);
         }
         assertTrue(AbstractTestGenerator.isSolverAvailable());
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotGenerateTestsJobTest_testTestGeneration");
         IFolder src = project.getProject().getFolder(JDTUtil.getSourceFolderName());
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/magic42", src);
         TestUtilsUtil.waitForBuild();
         IFile proofFile = src.getFile("IntegerUtil.proof");
         assertTrue(proofFile.exists());
         // Generate test cases
         GenerateTestsJob job = new GenerateTestsJob(proofFile);
         job.schedule();
         TestUtilsUtil.waitForJobs();
         // Test generated stuff
         IProject testProject = ResourcesPlugin.getWorkspace().getRoot().getProject(project.getProject().getName() + EclipseTestGenerator.TEST_PROJECT_SUFFIX);
         TestUtilsUtil.waitForProject(bot, testProject);
         bot.waitUntil(Conditions.waitForEditor(Matchers.<IEditorReference>anything()));
         assertTrue(testProject.exists());
         assertTrue(testProject.isOpen());
         // Test library folder
         IFolder libFolder = testProject.getFolder(EclipseTestGenerator.LIB_FOLDER_NAME);
         assertTrue(libFolder.exists());
         IFile readmeFile = libFolder.getFile(EclipseTestGenerator.LIB_FOLDER_README_NAME);
         assertTrue(readmeFile.exists());
         assertEquals(IOUtil.readFrom(EclipseTestGenerator.createLibFolderReadmeContent()), ResourceUtil.readFrom(readmeFile));
         // Test log folder
         IFolder logFolder = testProject.getFolder(EclipseTestGenerator.LOG_FOLDER_NAME);
         assertTrue(logFolder.exists());
         IFile logFile = logFolder.getFile(ResourceUtil.getFileNameWithoutExtension(proofFile) + EclipseTestGenerator.LOG_FILE_EXTENSION_WITH_DOT);
         assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(logFile)));
         // Test src folder
         IFolder srcFolder = testProject.getFolder(JDTUtil.getSourceFolderName());
         assertTrue(srcFolder.exists());
         IFile sourceFile = srcFolder.getFile(ResourceUtil.getFileNameWithoutExtension(proofFile) + TestCaseGenerator.JAVA_FILE_EXTENSION_WITH_DOT);
         assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(sourceFile)));
         // Test opened editor
         IEditorInput input = bot.activeEditor().getReference().getEditorInput();
         assertEquals(sourceFile, input.getAdapter(IFile.class));
      }
      finally {
         bot.closeAllEditors();
      }
   }
}
