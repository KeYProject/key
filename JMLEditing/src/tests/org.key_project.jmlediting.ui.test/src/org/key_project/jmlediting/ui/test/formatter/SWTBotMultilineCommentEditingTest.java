package org.key_project.jmlediting.ui.test.formatter;

import static org.junit.Assert.assertEquals;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;

public class SWTBotMultilineCommentEditingTest {

   private static SWTWorkbenchBot bot;
   private static TestProject testProject;

   private static SWTBotEclipseEditor editor;

   @BeforeClass
   public static void initializeProject() throws CoreException,
         InterruptedException {
      bot = new SWTWorkbenchBot();
      testProject = JMLEditingUITestUtils.createProjectWithFile(bot,
            "MultilineCommentEditing", "test", "MultilineCommentEditingTest",
            SaveGuarantee.NO_SAVE);
   }

   @Before
   public void refreshEditor() throws CoreException {
      testProject.restoreClassAndOpen();
      editor = testProject.getOpenedEditor();
   }
   
   @AfterClass
   public static void closeEditor() {
      editor.close();
   }

   @Test
   public void testInsertNewLineJML1() {
      this.typeTextAndCheckNextLine(14, 29, "\n",
            "New line after new line in JML is wrong", "     @ ");
   }

   @Test
   public void testInsertNewLineJML2() {
      this.typeTextAndCheckNextLine(15, 22, "\n",
            "Indentation of new line in JML is wrong", "     @   ");
   }

   @Test
   public void testInsertNewLineEndJML() {
      this.typeTextAndCheckNextLine(17, 6, "\n",
            "New line at last line in JML caused wrong new line.", "     @*/");
   }

   @Test
   public void testNewLineInLineJML() {
      this.typeTextAndCheckNextLine(16, 20, "\n",
            "Newline in text for JML wrong.", "     @   c;");
   }

   @Test
   public void testCreateJMLComment() {
      editor.insertText(24, 3, "/*@");
      editor.typeText(24, 6, "\n");
      final String nextLine = editor.getTextOnLine(25);
      assertEquals("Next line when opening new JML comment is wrong",
            "     @ ", nextLine);
      final String closingLine = editor.getTextOnLine(26);
      assertEquals("Closing line of opened JML commend is wrong", "     @*/",
            closingLine);
   }

   @Test
   public void testInsertNewLineSingleLineJML() {
      this.typeTextAndCheckNextLine(25, 29, "\n",
            "In single line no @ should be generated", "   ");
   }

   @Test
   public void testNewLineJavaDoc() {
      this.typeTextAndCheckNextLine(19, 31, "\n", "New line in Javadoc wrong",
            "    * ");
   }

   @Test
   public void testNewLineNormalComment() {
      this.typeTextAndCheckNextLine(5, 42, "\n", "No line in Javadoc wrong",
            "    * ");
   }

   private void typeTextAndCheckNextLine(final int line, final int column,
         final String text, final String message, final String requiredNextLine) {
      editor.typeText(line, column, text);
      final String nextLine = editor.getTextOnLine(line + 1);
      assertEquals(message, requiredNextLine, nextLine);
   }

}
