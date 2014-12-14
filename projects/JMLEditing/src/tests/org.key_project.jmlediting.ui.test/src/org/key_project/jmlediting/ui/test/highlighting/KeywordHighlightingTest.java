package org.key_project.jmlediting.ui.test.highlighting;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.keyboard.Keystrokes;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.Activator;
import org.key_project.jmlediting.ui.test.TestUtils;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

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
public class KeywordHighlightingTest {

   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private SWTBotEclipseEditor editor = null;

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
   private static final Position requiresJMLMline = new Position(31, 10);
   private static final Position requiresJavaCode = new Position(34, 6);
   private static final Position requiresJMLSLine = new Position(33, 10);

   private static final Position noKWJavaSLine = new Position(43, 9);
   private static final Position noKWJavaDoc = new Position(38, 9);
   private static final Position noKWJavaMLine = new Position(41, 9);
   private static final Position noKWJMLMline = new Position(47, 10);
   private static final Position noKWJavaCode = new Position(48, 6);
   private static final Position noKWJMLSLine = new Position(47, 10);

   private static final int fontStyleBoldKeyWord = 1;

   /*
    * Initialize a new Project and load the template class from data/template
    * with all kinds of Comments to test AutoCompletion in and open it.
    */
   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      final IJavaProject project = TestUtilsUtil
            .createJavaProject(PROJECT_NAME);
      final IFolder srcFolder = project.getProject().getFolder("src");
      final IFolder testFolder = TestUtilsUtil.createFolder(srcFolder,
            PACKAGE_NAME);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID,
            "data/template", testFolder);
      bot.tree().getTreeItem(PROJECT_NAME).select().expand().getNode("src")
      .select().expand().getNode(PACKAGE_NAME).select().expand()
      .getNode(CLASS_NAME + ".java").select().doubleClick();
      JMLPreferencesHelper.setProjectJMLProfile(project.getProject(),
            TestUtils.findReferenceProfile());
   }

   /*
    * just make sure the global variable editor is set and setting the Colors
    * for Testing
    */
   @Before
   public void initEditor() {
      this.editor = bot.activeEditor().toTextEditor();
   }

   /*
    * removes the text with given length at Position pos
    */
   private void removeText(final int line, final int column, final int length) {
      this.editor.selectRange(line, column, length);
      bot.sleep(100);
      this.editor.pressShortcut(Keystrokes.DELETE);
   }

   @Test
   public void ensuresBeforeChangesTest() {
      assertFalse("Ensures Keyword was Bold but should not have been",
            this.isBold(ensuresJavaCode.line, ensuresJavaCode.column, 7));
      assertFalse("Ensures Keyword was Bold but should not have been",
            this.isBold(ensuresJavaDoc.line, ensuresJavaDoc.column, 7));
      assertFalse("Ensures Keyword was Bold but should not have been",
            this.isBold(ensuresJavaMLine.line, ensuresJavaMLine.column, 7));
      assertFalse("Ensures Keyword was Bold but should not have been",
            this.isBold(ensuresJavaSLine.line, ensuresJavaSLine.column, 7));
      assertTrue("Ensures Keyword was not Bold but should have been",
            this.isBold(ensuresJMLSLine.line, ensuresJMLSLine.column, 7));
      assertTrue("Ensures Keyword was not Bold but should have been",
            this.isBold(ensuresJMLMline.line, ensuresJMLMline.column, 7));
   }

   @Test
   public void requiresBeforeChangesTest() {
      assertFalse("requires Keyword was Bold but should not have been",
            this.isBold(requiresJavaCode.line, requiresJavaCode.column, 8));
      assertFalse("requires Keyword was Bold but should not have been",
            this.isBold(requiresJavaDoc.line, requiresJavaDoc.column, 8));
      assertFalse("requires Keyword was Bold but should not have been",
            this.isBold(requiresJavaMLine.line, requiresJavaMLine.column, 8));
      assertFalse("requires Keyword was Bold but should not have been",
            this.isBold(requiresJavaSLine.line, requiresJavaSLine.column, 8));
      assertTrue("requires Keyword was not Bold but should have been",
            this.isBold(requiresJMLSLine.line, requiresJMLSLine.column, 8));
      assertTrue("requires Keyword was not Bold but should have been",
            this.isBold(requiresJMLMline.line, requiresJMLMline.column, 8));
   }

   @Test
   public void nonKWBeforeChangesTest() {
      assertFalse("Non Keyword was Bold but should not have been",
            this.isBold(noKWJavaCode.line, noKWJavaCode.column, 4));
      assertFalse("Non Keyword was Bold but should not have been",
            this.isBold(noKWJavaDoc.line, noKWJavaDoc.column, 4));
      assertFalse("Non Keyword was Bold but should not have been",
            this.isBold(noKWJavaMLine.line, noKWJavaMLine.column, 4));
      assertFalse("Non Keyword was Bold but should not have been",
            this.isBold(noKWJavaSLine.line, noKWJavaSLine.column, 4));
      assertFalse("Non Keyword was Bold but should not have been",
            this.isBold(noKWJMLSLine.line, noKWJMLSLine.column, 4));
      assertFalse("Non Keyword was Bold but should not have been",
            this.isBold(noKWJMLMline.line, noKWJMLMline.column, 4));
   }

   @Test
   public void ensuresKeywordAfterChangesTest() {
      this.changeDocument();
      assertFalse("ensures keyword was bold but should not have been",
            this.isBold(ensuresJMLMline.line, ensuresJMLMline.column, 7));
      assertTrue("ensures keyword was not bold but should have been",
            this.isBold(ensuresJavaMLine.line, ensuresJavaMLine.column, 7));
      assertFalse("requires keyword was bold but should not have been",
            this.isBold(requiresJMLMline.line, requiresJMLMline.column, 8));
      assertTrue("ensures keyword was not bold but should have been",
            this.isBold(ensuresJavaDoc.line, ensuresJavaDoc.column, 7));
      assertFalse("requires keyword was bold but should not have been",
            this.isBold(requiresJavaDoc.line, requiresJavaDoc.column, 8));
      assertFalse("requires keyword was bold but should not have been",
            this.isBold(requiresJavaMLine.line, requiresJavaMLine.column, 8));
      assertTrue("ensures Keyword was not bold but should have been",
            this.isBold(ensuresJavaSLine.line, ensuresJavaSLine.column + 1, 7));
      assertFalse("ensuresKeyword was bold but should not have been",
            this.isBold(ensuresJMLSLine.line, ensuresJMLSLine.column - 1, 7));
      this.revertChanges();
   }

   /**
    * provides the needed changes for the test
    */
   public void changeDocument() {
      this.removeText(ensuresJMLMline.line - 1, 5, 1);

      this.editor.insertText(ensuresJavaMLine.line - 1, 5, "@");
      this.removeText(ensuresJavaMLine.line, 4, 1);
      this.editor.insertText(ensuresJavaMLine.line, 4, "@");
      this.editor.insertText(ensuresJavaMLine.line + 1, 4, "@");

      this.removeText(requiresJMLMline.line - 1, 8, 1);
      this.editor.insertText(requiresJMLMline.line - 1, 8, "*");

      this.removeText(ensuresJavaDoc.line - 2, 2, 1);
      this.editor.insertText(ensuresJavaDoc.line - 2, 2, "@");
      this.removeText(ensuresJavaDoc.line - 1, 1, 1);
      this.removeText(ensuresJavaDoc.line, 1, 1);
      this.removeText(ensuresJavaDoc.line + 1, 1, 1);
      this.editor.insertText(ensuresJavaDoc.line - 1, 1, "@");
      this.editor.insertText(ensuresJavaDoc.line, 1, "@");
      this.editor.insertText(ensuresJavaDoc.line + 1, 1, "@");
      this.editor.insertText(ensuresJavaDoc.line + 2, 1, "@");

      this.removeText(requiresJavaDoc.line - 1, 8, 1);

      this.editor.insertText(requiresJavaMLine.line - 1, 8, "*");

      this.editor.insertText(ensuresJavaSLine.line,
            ensuresJavaSLine.column - 1, "@");
      this.removeText(ensuresJMLSLine.column, ensuresJMLSLine.column - 2, 1);
   }

   /**
    * reverts the changes to guarantee the documents integrity for other tests
    */
   public void revertChanges() {
      this.editor.insertText(ensuresJMLMline.line - 1, 5, "@");

      this.removeText(ensuresJavaMLine.line - 1, 5, 1);
      this.removeText(ensuresJavaMLine.line, 4, 1);
      this.removeText(ensuresJavaMLine.line + 1, 4, 1);
      this.editor.insertText(ensuresJavaMLine.line, 4, "*");

      this.removeText(requiresJMLMline.line - 1, 8, 1);
      this.editor.insertText(requiresJavaMLine.line - 1, 8, "@");

      this.removeText(ensuresJavaDoc.line - 2, 2, 1);
      this.editor.insertText(ensuresJavaDoc.line - 2, 2, "*");
      this.removeText(ensuresJavaDoc.line - 1, 1, 1);
      this.removeText(ensuresJavaDoc.line, 1, 1);
      this.removeText(ensuresJavaDoc.line + 1, 1, 1);
      this.editor.insertText(ensuresJavaDoc.line - 1, 1, "*");
      this.editor.insertText(ensuresJavaDoc.line, 1, "*");
      this.editor.insertText(ensuresJavaDoc.line + 1, 1, "*");
      this.removeText(ensuresJavaDoc.line + 2, 1, 1);

      this.editor.insertText(ensuresJavaDoc.line - 1, 8, "*");

      this.removeText(requiresJavaMLine.line - 1, 8, 1);

      this.removeText(ensuresJavaSLine.line, ensuresJavaSLine.column - 1, 1);

      this.editor.insertText(ensuresJMLSLine.column,
            ensuresJMLSLine.column - 2, "@");
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
   public boolean isBold(final int line, final int column, final int length) {
      final StyleRange[] styles = this.editor.getStyles(line, column, length);
      boolean bold = true;
      for (final StyleRange r : styles) {
         bold &= (r.fontStyle == fontStyleBoldKeyWord);
      }
      return bold;
   }
}
