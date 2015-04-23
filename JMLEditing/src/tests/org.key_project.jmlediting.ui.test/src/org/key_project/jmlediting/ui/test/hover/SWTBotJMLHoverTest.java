package org.key_project.jmlediting.ui.test.hover;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.ui.test.Activator;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotJMLHoverTest {

   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static final String PROJECT_NAME = "JMLHoverTestProject";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "HoverTestClass";

   private static IJMLProfile profile;

   private static SWTBotEclipseEditor editor;

   @BeforeClass
   public static void createProject() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();
      final IJavaProject project = TestUtilsUtil.createJavaProject(PROJECT_NAME);
      JMLPreferencesHelper.setProjectJMLProfile(project.getProject(), JMLEditingUITestUtils.findReferenceProfile());
      profile = JMLPreferencesHelper.getProjectActiveJMLProfile(project.getProject());
      final IFolder testFolder = TestUtilsUtil.createFolder(project.getProject().getFolder("src"), PACKAGE_NAME);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/template/" + CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT, testFolder, true);
      TestUtilsUtil.waitForBuild();
      TestUtilsUtil.openEditor(testFolder.getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
      editor = bot.activeEditor().toTextEditor();
   }

   @Test
   public void testKeywordHover() throws IOException {
      // Read to hover file
      List<String[]> testData = new ArrayList<String[]>();
      String testContent = IOUtil.readFrom(BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/KeywordHoverData.txt"));
      StringTokenizer tokenizer = new StringTokenizer(testContent, "\n\r");
      while (tokenizer.hasMoreTokens()) {
         String nextLine = tokenizer.nextToken();
         testData.add(nextLine.split("-"));
      }
      // Perform test.
      for (final String[] data : testData) {
         final int line = Integer.parseInt(data[0]) - 1;
         final int column = Integer.parseInt(data[1]);
         final String expectedKeyword = data[2];
         final String hoverText = JMLEditingUITestUtils.getHoverAtPosition(bot, editor, line, column);
         final IKeyword keyword = JMLProfileHelper.findKeyword(profile, expectedKeyword);
         if (keyword == null) {
            assertNull("Got hover for no keyword at " + line + " " + column, hoverText);
         }
         else if (hoverText == null) {
            fail("Got no hover for keyword '" + expectedKeyword + "' at " + line + " " + column);
         }
         else {
            final String cleanedHoverText = hoverText.replace("\n", "").replace(" ", "");
            final String cleanedDescriptionText = keyword.getDescription().replace("\n", "").replace(" ", "");
            assertEquals("Got wrong hover text at " + line + " " + column, cleanedDescriptionText, cleanedHoverText);
         }
      }
   }
   
   @AfterClass
   public static void closeEditor() {
      editor.close();
   }
}
