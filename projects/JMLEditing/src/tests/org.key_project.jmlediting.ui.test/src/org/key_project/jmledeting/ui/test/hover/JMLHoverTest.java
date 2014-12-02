package org.key_project.jmledeting.ui.test.hover;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.ui.test.Activator;
import org.key_project.jmlediting.ui.test.TestUtils;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class JMLHoverTest {

   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static final String PROJECT_NAME = "JMLHoverTestProject";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "HoverTestClass";

   private static IJMLProfile profile;

   private static SWTBotEclipseEditor editor;

   @BeforeClass
   public static void createProject() throws CoreException,
   InterruptedException {
      final IJavaProject project = TestUtilsUtil
            .createJavaProject(PROJECT_NAME);
      final IFolder testFolder = TestUtilsUtil.createFolder(project
            .getProject().getFolder("src"), PACKAGE_NAME);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID,
            "data/template/" + CLASS_NAME + ".java", testFolder);
      TestUtils.selectFileInProject(bot, PROJECT_NAME, "src/test/" + CLASS_NAME
            + ".java");
      editor = bot.activeEditor().toTextEditor();
      JMLPreferencesHelper.setProjectJMLProfile(project.getProject(),
            TestUtils.findReferenceProfile());
      profile = JMLPreferencesHelper.getProjectActiveJMLProfile(project
            .getProject());
   }

   @Test
   public void testKeywordHover() throws IOException {
      // Read to hover file
      final BufferedReader reader = new BufferedReader(new InputStreamReader(
            BundleUtil.openInputStream(Activator.PLUGIN_ID,
                  "data/KeywordHoverData.txt")));
      String tmp;
      final List<String[]> testData = new ArrayList<String[]>();
      while ((tmp = reader.readLine()) != null) {
         testData.add(tmp.split("-"));
      }

      for (final String[] data : testData) {
         final int line = Integer.parseInt(data[0]) - 1;
         final int column = Integer.parseInt(data[1]);
         final String expectedKeyword = data[2];

         final String hoverText = TestUtils.getHoverAtPosition(bot, editor,
               line, column);

         final IKeyword keyword = JMLProfileHelper.findKeyword(profile,
               expectedKeyword);

         if (keyword == null) {
            assertNull("Got hover for no keyword at " + line + " " + column,
                  hoverText);
         }
         else if (hoverText == null) {
            fail("Got no hover for keyword at " + line + " " + column);
         }
         else {
            final String cleanedHoverText = hoverText.replace("\n", "")
                  .replace(" ", "");
            final String cleanedDescriptionText = keyword.getDescription()
                  .replace("\n", "").replace(" ", "");
            assertEquals("Got wrong hover text at " + line + " " + column,
                  cleanedDescriptionText, cleanedHoverText);
         }

      }

   }
}
