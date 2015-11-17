package org.key_project.jmlediting.ui.test.formatter;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotFormatterTest {

   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   private static SWTBotEclipseEditor editor;

   private static TestProject project;

   @BeforeClass
   public static void createProject() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();
      project = JMLEditingUITestUtils.createProjectWithFile(bot, 
                                                            "SWTBotFormatterTest", 
                                                            "org.key_project.jmlediting.ui.test.formatter", 
                                                            "FormatterTest", 
                                                            SaveGuarantee.NO_SAVE);
   }

   @Before
   public void openEditor() throws CoreException {
      project.restoreClassAndOpen();
      editor = project.getOpenedEditor();
   }
   
   @AfterClass
   public static void closeEditor() {
      editor.close();
   }

   @Test
   public void testJMLCommentsUnchanged() {
      final List<String> commentsBefore = this.getComments();
      editor.contextMenu("Source").menu("Format Element").click();
      TestUtilsUtil.waitForJobs();
      final List<String> commentAfter = this.getComments();
      assertEquals("Formatter modified JML comments", commentsBefore, commentAfter);
   }

   @Test
   public void testJMLCommentsUnchangedFormatElement() {
      final List<String> commentsBefore = this.getComments();  
      editor.selectRange(18, 12, 121);
      editor.contextMenu("Source").menu("Format Element").click();
      TestUtilsUtil.waitForJobs();
      final List<String> commentAfter = this.getComments();
      assertEquals("Format element modified JML comments", commentsBefore, commentAfter);
   }

   private List<String> getComments() {
      final List<String> comments = new ArrayList<String>();
      for (final CommentRange range : JMLEditingUITestUtils.getAllJMLCommentsInEditor(editor)) {
         comments.add(editor.getText().substring(range.getBeginOffset(), range.getEndOffset() + 1));
      }
      return comments;
   }

}
