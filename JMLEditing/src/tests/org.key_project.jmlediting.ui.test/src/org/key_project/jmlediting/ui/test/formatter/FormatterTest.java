package org.key_project.jmlediting.ui.test.formatter;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.test.UITestUtils;
import org.key_project.jmlediting.ui.test.UITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.UITestUtils.TestProject.SaveGuarantee;

public class FormatterTest {

   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   private SWTBotEclipseEditor editor;

   private static TestProject project;

   @BeforeClass
   public static void createProject() throws CoreException,
         InterruptedException {
      project = UITestUtils.createProjectWithFile(bot, FormatterTest.class,
            SaveGuarantee.NO_SAVE);
   }

   @Before
   public void openEditor() throws CoreException {
      project.restoreClassAndOpen();
      this.editor = project.getOpenedEditor();
   }

   @Test
   public void testJMLCommentsUnchanged() {
      final List<String> commentsBefore = this.getComments();
      bot.menu("Source").menu("Format").click();
      bot.sleep(1000);
      final List<String> commentAfter = this.getComments();
      assertEquals("Formatter modified JML comments", commentsBefore,
            commentAfter);
   }

   @Test
   public void testJMLCommentsUnchangedFormatElement() {
      final List<String> commentsBefore = this.getComments();
      this.editor.selectRange(18, 12, 121);
      bot.menu("Source").menu("Format Element").click();
      bot.sleep(1000);
      final List<String> commentAfter = this.getComments();
      assertEquals("Format element modified JML comments", commentsBefore,
            commentAfter);
   }

   private List<String> getComments() {
      final List<String> comments = new ArrayList<String>();
      for (final CommentRange range : UITestUtils
            .getAllJMLCommentsInEditor(this.editor)) {
         comments.add(this.editor.getText().substring(range.getBeginOffset(),
               range.getEndOffset() + 1));
      }
      return comments;
   }

}
