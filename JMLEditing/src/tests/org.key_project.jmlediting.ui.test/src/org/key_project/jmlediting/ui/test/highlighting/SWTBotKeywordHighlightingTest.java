package org.key_project.jmlediting.ui.test.highlighting;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.keyboard.Keystrokes;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;

/**
 *
 * @author David Giessing Testingplan for Keyword Highlighting Test: </br> Check
 *         Keyword Highlighting for "ensures" in the different Sections:<br/>
 *         <ul>
 *         <li>Keyword ensures in JMLSingleLineComment</li>
 *         <li>Keyword ensures in JMLMultiLineComment</li>
 *         <li>Keyword ensures in JavaDoc</li>
 *         <li>Keyword ensures in JavaSingleLineComment</li>
 *         <li>Keyword ensures in JavaMultiLineComment</li>
 *         <li>Keyword ensures in JavaCode</li>
 *         </ul>
 *         </br> Check Keyword Highlighting for "requires" in the different
 *         Sections: <br/>
 *         <ul>
 *         <li>Keyword requires in JMLSingleLineComment</li>
 *         <li>Keyword requires in JMLMultiLineComment</li>
 *         <li>Keyword requires in JavaDoc</li>
 *         <li>Keyword requires in JavaSingleLineComment</li>
 *         <li>Keyword requires in JavaMultiLineComment</li>
 *         <li>Keyword requires in JavaCode
 *         </ul>
 *         </br> Check non Keyword in the different Sections:<br/>
 *         <ul>
 *         <li>Non Keyword in JMLSingleLineComment</li>
 *         <li>Non Keyword in JavaSingleLinecomment</li>
 *         <li>Non Keyword in JMLMultilineComment</li>
 *         <li>Non Keyword in JavaMultilinecomment</li>
 *         <li>Non Keyword in JavaDoc</li>
 *         </ul>
 *         </br> Check Keyword ensures in different Sections after Changes<br/>
 *         <ul>
 *         <li>Keyword ensures after change from JMLSingleLine to JavaSingleLine
 *         </li>
 *         <li>Keyword ensures after change from JavaSingleLine to JMLSingleLine
 *         </li>
 *         <li>Keyword after change from JMLMultiLine to JavaMultiLine</li>
 *         <li>Keyword after change from JavaMultiLine to JMLMultiLine</li>
 *         <li>Keyword after change from JMLMultiLine to JavaDoc</li>
 *         <li>Keyword after change from JavaDoc to JMLMultiLine</li>
 *         <li>Keyword after change from JavaDoc to JavaMultiLine</li>
 *         <li>Keyword after change from JavaMultiLine to JavaDoc</li>
 *         <li>Keyword after change from JavaSingleLine to JMLSingleLine</li>
 *         <li>Keyword after change from JMLSingleLine to JavaSingleLine</li>
 *         </ul>
 */
public class SWTBotKeywordHighlightingTest {

   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static SWTBotEclipseEditor editor = null;

   private static final String PROJECT_NAME = "TestKeywordHighlighting";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "KeywordHighlightingTestClass";

   private static final Position ensuresJavaSLine = new Position(2, 3);
   private static final Position ensuresJavaDoc = new Position(6, 3);
   private static final Position ensuresJavaMLine = new Position(11, 6);
   private static final Position ensuresJMLMline = new Position(14, 7);
   private static final Position ensuresJavaCode = new Position(19, 6);
   private static final Position ensuresJMLSLine = new Position(20, 10);

   private static final Position requiresJavaSLine = new Position(29, 9);
   private static final Position requiresJavaDoc = new Position(24, 9);
   private static final Position requiresJavaMLine = new Position(27, 9);
   private static final Position requiresJMLMline = new Position(32, 10);
   private static final Position requiresJavaCode = new Position(36, 6);
   private static final Position requiresJMLSLine = new Position(35, 10);

   private static final Position noKWJavaSLine = new Position(45, 9);
   private static final Position noKWJavaDoc = new Position(40, 9);
   private static final Position noKWJavaMLine = new Position(43, 9);
   private static final Position noKWJMLMline = new Position(47, 10);
   private static final Position noKWJavaCode = new Position(50, 6);
   private static final Position noKWJMLSLine = new Position(49, 10);

   private static final int fontStyleBoldKeyWord = 1;

   /*
    * Initialize a new Project and load the template class from data/template
    * with all kinds of Comments to test AutoCompletion in and open it.
    */
   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      final JMLEditingUITestUtils.TestProject result = JMLEditingUITestUtils.createProjectWithFile(
            bot, PROJECT_NAME, PACKAGE_NAME, CLASS_NAME, SaveGuarantee.NO_SAVE);
      JMLPreferencesHelper.setProjectJMLProfile(result.getProject()
            .getProject(), JMLEditingUITestUtils.findReferenceProfile());
      result.restoreClassAndOpen();
      editor = result.getOpenedEditor();
   }
   
   @AfterClass
   public static void closeEditor() {
      editor.close();
   }

   private static void removeText(final int line, final int column, final int length) {
      editor.selectRange(line, column, length);
      editor.pressShortcut(Keystrokes.DELETE);
   }

   @Test
   public void ensuresBeforeChangesTest() {
      assertFalse("Ensures Keyword was Bold but should not have been",
            isBold(ensuresJavaCode.line, ensuresJavaCode.column, 7));
      assertFalse("Ensures Keyword was Bold but should not have been",
            isBold(ensuresJavaDoc.line, ensuresJavaDoc.column, 7));
      assertFalse("Ensures Keyword was Bold but should not have been",
            isBold(ensuresJavaMLine.line, ensuresJavaMLine.column, 7));
      assertFalse("Ensures Keyword was Bold but should not have been",
            isBold(ensuresJavaSLine.line, ensuresJavaSLine.column, 7));
      assertTrue("Ensures Keyword was not Bold but should have been",
            isBold(ensuresJMLSLine.line, ensuresJMLSLine.column, 7));
      assertTrue("Ensures Keyword was not Bold but should have been",
            isBold(ensuresJMLMline.line, ensuresJMLMline.column, 7));
   }

   @Test
   public void requiresBeforeChangesTest() {
      assertFalse("requires Keyword was Bold but should not have been",
            isBold(requiresJavaCode.line, requiresJavaCode.column, 8));
      assertFalse("requires Keyword was Bold but should not have been",
            isBold(requiresJavaDoc.line, requiresJavaDoc.column, 8));
      assertFalse("requires Keyword was Bold but should not have been",
            isBold(requiresJavaMLine.line, requiresJavaMLine.column, 8));
      assertFalse("requires Keyword was Bold but should not have been",
            isBold(requiresJavaSLine.line, requiresJavaSLine.column, 8));
      assertTrue("requires Keyword was not Bold but should have been",
            isBold(requiresJMLSLine.line, requiresJMLSLine.column, 8));
      assertTrue("requires Keyword was not Bold but should have been",
            isBold(requiresJMLMline.line, requiresJMLMline.column, 8));
   }

   @Test
   public void nonKWBeforeChangesTest() {
      assertFalse("Non Keyword was Bold but should not have been",
            isBold(noKWJavaCode.line, noKWJavaCode.column, 4));
      assertFalse("Non Keyword was Bold but should not have been",
            isBold(noKWJavaDoc.line, noKWJavaDoc.column, 4));
      assertFalse("Non Keyword was Bold but should not have been",
            isBold(noKWJavaMLine.line, noKWJavaMLine.column, 4));
      assertFalse("Non Keyword was Bold but should not have been",
            isBold(noKWJavaSLine.line, noKWJavaSLine.column, 4));
      assertFalse("Non Keyword was Bold but should not have been",
            isBold(noKWJMLSLine.line, noKWJMLSLine.column, 4));
      assertFalse("Non Keyword was Bold but should not have been",
            isBold(noKWJMLMline.line, noKWJMLMline.column, 4));
   }

   @Test
   public void ensuresKeywordAfterChangesTest() {
      changeDocument();
      assertFalse("ensures keyword was bold but should not have been",
            isBold(ensuresJMLMline.line, ensuresJMLMline.column, 7));
      assertTrue("ensures keyword was not bold but should have been",
            isBold(ensuresJavaMLine.line, ensuresJavaMLine.column, 7));
      assertFalse("requires keyword was bold but should not have been",
            isBold(requiresJMLMline.line, requiresJMLMline.column, 8));
      assertTrue("ensures keyword was not bold but should have been",
            isBold(ensuresJavaDoc.line, ensuresJavaDoc.column, 7));
      assertFalse("requires keyword was bold but should not have been",
            isBold(requiresJavaDoc.line, requiresJavaDoc.column, 8));
      assertFalse("requires keyword was bold but should not have been",
            isBold(requiresJavaMLine.line, requiresJavaMLine.column, 8));
      assertTrue("ensures Keyword was not bold but should have been",
            isBold(ensuresJavaSLine.line, ensuresJavaSLine.column + 1, 7));
      assertFalse("ensuresKeyword was bold but should not have been",
            isBold(ensuresJMLSLine.line, ensuresJMLSLine.column - 1, 7));
      revertChanges();
   }

   /**
    * provides the needed changes for the test
    */
   private static void changeDocument() {
      removeText(ensuresJMLMline.line - 1, 5, 1);

      editor.insertText(ensuresJavaMLine.line - 1, 5, "@");
      removeText(ensuresJavaMLine.line, 4, 1);
      editor.insertText(ensuresJavaMLine.line, 4, "@");
      editor.insertText(ensuresJavaMLine.line + 1, 4, "@");

      removeText(requiresJMLMline.line - 1, 8, 1);
      editor.insertText(requiresJMLMline.line - 1, 8, "*");

      removeText(ensuresJavaDoc.line - 2, 2, 1);
      editor.insertText(ensuresJavaDoc.line - 2, 2, "@");
      removeText(ensuresJavaDoc.line - 1, 1, 1);
      removeText(ensuresJavaDoc.line, 1, 1);
      removeText(ensuresJavaDoc.line + 1, 1, 1);
      editor.insertText(ensuresJavaDoc.line - 1, 1, "@");
      editor.insertText(ensuresJavaDoc.line, 1, "@");
      editor.insertText(ensuresJavaDoc.line + 1, 1, "@");
      editor.insertText(ensuresJavaDoc.line + 2, 1, "@");

      removeText(requiresJavaDoc.line - 1, 8, 1);

      editor.insertText(requiresJavaMLine.line - 1, 8, "*");

      editor.insertText(ensuresJavaSLine.line, ensuresJavaSLine.column - 1, "@");
      removeText(ensuresJMLSLine.line, ensuresJMLSLine.column - 2, 1);
   }

   /**
    * reverts the changes to guarantee the documents integrity for other tests
    */
   private static void revertChanges() {
      editor.insertText(ensuresJMLMline.line - 1, 5, "@");

      removeText(ensuresJavaMLine.line - 1, 5, 1);
      removeText(ensuresJavaMLine.line, 4, 1);
      editor.insertText(ensuresJavaMLine.line, 4, "*");
      removeText(ensuresJavaMLine.line + 1, 4, 1);

      removeText(requiresJMLMline.line - 1, 8, 1);
      editor.insertText(requiresJMLMline.line - 1, 8, "@");

      removeText(ensuresJavaDoc.line - 2, 2, 1);
      editor.insertText(ensuresJavaDoc.line - 2, 2, "*");
      removeText(ensuresJavaDoc.line - 1, 1, 1);
      removeText(ensuresJavaDoc.line, 1, 1);
      removeText(ensuresJavaDoc.line + 1, 1, 1);
      removeText(ensuresJavaDoc.line + 2, 1, 1);
      editor.insertText(ensuresJavaDoc.line - 1, 1, "*");
      editor.insertText(ensuresJavaDoc.line, 1, "*");
      editor.insertText(ensuresJavaDoc.line + 1, 1, "*");
      removeText(ensuresJavaDoc.line + 2, 1, 1);

      editor.insertText(ensuresJavaDoc.line - 1, 8, "*");

      removeText(requiresJavaMLine.line - 1, 8, 1);

      removeText(ensuresJavaSLine.line, ensuresJavaSLine.column - 1, 1);

      editor.insertText(ensuresJMLSLine.line, ensuresJMLSLine.column - 2, "@");
   }

   /**
    * Checks whether the whole part beginning at offset with length length in
    * the TestClass is in Bold Style
    *
    * @param line
    *           the line where to begin checking
    * @param column
    *           the column in line where to begin checking
    * @param length
    *           the length to check
    * @return true if whole part is written in Bold Style, false when one or
    *         more characters are not in Bold style
    */
   private static boolean isBold(final int line, final int column,
         final int length) {
      final StyleRange[] styles = editor.getStyles(line, column, length);
      boolean bold = true;
      for (final StyleRange r : styles) {
         bold &= (r.fontStyle == fontStyleBoldKeyWord);
      }
      return bold;
   }
}
