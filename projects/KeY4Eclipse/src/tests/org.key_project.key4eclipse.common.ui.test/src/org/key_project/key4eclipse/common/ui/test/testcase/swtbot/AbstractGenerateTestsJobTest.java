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
import org.key_project.key4eclipse.common.ui.testGeneration.EclipseTestGenerator;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.testgen.TestCaseGenerator;

/**
 * Provides the basic functionality to test test case generation.
 * @author Martin Hentschel
 */
public class AbstractGenerateTestsJobTest extends TestCase {   
   /**
    * Ensures that the created project is correct.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param sourceProject The name of the source {@link IProject}.
    * @param testCaseName The name of the test case.
    * @throws Exception Occurred Exception.
    */
   protected void assertTestProjectAndOpenedEditor(SWTWorkbenchBot bot, IJavaProject sourceProject, String testCaseName) throws Exception {
      // Test generated stuff
      IProject testProject = ResourcesPlugin.getWorkspace().getRoot().getProject(sourceProject.getProject().getName() + EclipseTestGenerator.TEST_PROJECT_SUFFIX);
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
      IFile logFile = logFolder.getFile(JDTUtil.ensureValidJavaTypeName(testCaseName, sourceProject) + EclipseTestGenerator.LOG_FILE_EXTENSION_WITH_DOT);
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(logFile)));
      // Test src folder
      IFolder srcFolder = testProject.getFolder(JDTUtil.getSourceFolderName());
      assertTrue(srcFolder.exists());
      IFile sourceFile = srcFolder.getFile(JDTUtil.ensureValidJavaTypeName(testCaseName, sourceProject) + TestCaseGenerator.JAVA_FILE_EXTENSION_WITH_DOT);
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(sourceFile)));
      // Test opened editor
      IEditorInput input = bot.activeEditor().getReference().getEditorInput();
      assertEquals(sourceFile, input.getAdapter(IFile.class));
   }
}
