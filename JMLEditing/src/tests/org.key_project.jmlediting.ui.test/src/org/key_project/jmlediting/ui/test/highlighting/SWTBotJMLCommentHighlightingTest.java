package org.key_project.jmlediting.ui.test.highlighting;

import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.keyboard.Keystrokes;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper.ColorProperty;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Testingplan of JMLCommentHighlighting: </br> Test Comment Highlighting for
 * every possible Type <br/>
 * <ul>
 * <li>JavaDoc</li>
 * <li>JavaSingleLineComment</li>
 * <li>JavaMultiLineComment</li>
 * <li>JMLSingleLineComment</li>
 * <li>JMLMultiLineComment</li>
 * <li>Strings</li>
 * <li>Chars</li>
 * <li>JavaCode</li>
 * <li>public in Comment</li>
 * <li>public in JavaDoc</li>
 * <li>public in Javacode</li>
 * <li>public in JML</li>
 * </ul>
 * after changes:</br>
 * <ul>
 * <li>change from Java SingleLine to JML Single Line</li>
 * <li>change from JML SingleLine to Java SingleLine</li>
 * <li>change from JavaDoc to JML Multiline Comment</li>
 * <li>change from JML Multiline Comment to JavaDoc</li>
 * <li>change from JavaDoc Comment to Java Multiline Comment</li>
 * <li>change from Java Multiline Comment to JavaDoc Comment</li>
 * <li>public in Comment</li>
 * <li>public in JavaDoc</li>
 * <li>public in Javacode</li>
 * <li>public in JML</li>
 * </ul>
 *
 * @author David Giessing
 *
 */
public class SWTBotJMLCommentHighlightingTest {

   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static SWTBotEclipseEditor editor = null;

   private static final String PROJECT_NAME = "CommentHighlightingProject";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "HighlightingTestClass";

   // SWTBot uses strange offsets... according to JavaClass
   // data/template/TestClass.java
   private static final Position PosJDocComment = new Position(4, 0);
   private static final Position PosJCommentMulti = new Position(10, 3);
   private static final Position PosJMLCommentMulti = new Position(13, 3);
   private static final Position PosInString = new Position(20, 25);
   private static final Position PosJCommentSingle = new Position(19, 6);
   private static final Position PosInMethod = new Position(20, 6);
   private static final Position PosJMLCommentSingle = new Position(23, 6);
   private static final Position PosInChar = new Position(24, 14);
   private static final Position PublicJML = new Position(29, 6);
   private static final Position PublicJavaComment = new Position(36, 6);
   private static final Position PublicJavaDoc = new Position(33, 6);
   private static final Position PublicKeyword = new Position(26, 3);

   private final RGB javaCommentRGB = new RGB(63, 127, 95);
   private final RGB javaDocRGB = new RGB(63, 95, 191);
   private final RGB specialWordRGB = new RGB(127, 0, 85);
   private final RGB defaultTextRGB = new RGB(0, 0, 0);
   private final RGB string = new RGB(42, 0, 255);
   private final RGB character = new RGB(42, 0, 255);
   private final Set<RGB> jmlColors = new HashSet<RGB>(Arrays.asList(
         JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.COMMENT),
         JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.KEYWORD),
         JMLUiPreferencesHelper
               .getWorkspaceJMLColor(ColorProperty.TOPLEVEL_KEYWORD)));

   private static TestProject testProject;

   /*
    * Initialize a new Project and load the template class from data/template
    * with all kinds of Comments to test AutoCompletion in and open it.
    */
   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();
      testProject = JMLEditingUITestUtils.createProjectWithFile(bot, PROJECT_NAME,
            PACKAGE_NAME, CLASS_NAME, SaveGuarantee.NO_SAVE);

      JMLPreferencesHelper.setProjectJMLProfile(testProject.getProject()
            .getProject(), JMLEditingUITestUtils.findReferenceProfile());
   }

   /*
    * just make sure the global variable editor is set and setting the Colors
    * for Testing
    */
   @Before
   public void initEditor() throws CoreException {
      testProject.restoreClassAndOpen();
      editor = testProject.getOpenedEditor();
   }
   
   @AfterClass
   public static void closeEditor() {
      editor.close();
   }

   /*
    * removes the text with given length at Position pos
    */
   private void removeText(final Position pos, final int length) {
      editor.selectRange(pos.line, pos.column, length);
      editor.pressShortcut(Keystrokes.DELETE);
   }

   @Test
   public void JMLSingleLineTest() {
      this.checkColors(PosJMLCommentSingle.line, PosJMLCommentSingle.column,
            30, this.jmlColors, "Color did not Match JMLCommentColor");
   }

   @Test
   public void JMLMultiLineTest() {
      this.checkColors(PosJMLCommentMulti.line, PosJMLCommentMulti.column, 33,
            this.jmlColors, "Color did not Match JMLCommentColor");
   }

   @Test
   public void JavaSingleLineTest() {
      this.checkColors(PosJCommentSingle.line, PosJCommentSingle.column, 27,
            this.javaCommentRGB, "Color did not Match JavaCommentColor");
   }

   @Test
   public void JavaMultiLineTest() {
      this.checkColors(PosJCommentMulti.line, PosJCommentMulti.column, 49,
            this.javaCommentRGB, "Color did not Match JavaCommentColor");
   }

   @Test
   public void JavaDocTest() {
      this.checkColors(PosJDocComment.line, PosJDocComment.column, 45,
            this.javaDocRGB, "Color did not Match JavaDocColor");
   }

   @Test
   public void StringTest() {
      this.checkColors(PosInString.line, PosInString.column, 21, this.string,
            "Color did not Match String Color");
   }

   @Test
   public void JavaCodeTest() {
      this.checkColors(PosInMethod.line, PosInMethod.column, 7,
            this.defaultTextRGB, "Color did not Match default Color");
   }

   @Test
   public void CharTest() {
      this.checkColors(PosInChar.line, PosInChar.column, 3, this.character,
            "Color did not Match CharColor");
   }

   @Test
   public void changeJMLMLineToJavaMLineTest() {
      this.removeText(new Position(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2), 1);
      this.checkColors(PosJMLCommentMulti.line, PosJMLCommentMulti.column, 33,
            this.javaCommentRGB, "Color did not Match JavaCommentColor");
   }

   @Test
   public void changeJavaMLineToJMLMLineTest() {
      editor.insertText(PosJCommentMulti.line,
            PosJCommentMulti.column + 2, "@");
      this.checkColors(PosJCommentMulti.line, PosJCommentMulti.column, 50,
            this.jmlColors, "Color did not Match JMLCommentColor");
   }

   @Test
   public void changeJMLSLineToJavaSLineTest() {
      this.removeText(new Position(PosJMLCommentSingle.line,
            PosJMLCommentSingle.column + 2), 1);
      this.checkColors(PosJMLCommentSingle.line, PosJMLCommentSingle.column,
            29, this.javaCommentRGB, "Color did not Match JavaCommentColor");
   }

   @Test
   public void changeJavaSLineToJMLSLineTest() {
      editor.insertText(PosJCommentSingle.line,
            PosJCommentSingle.column + 2, "@");
      this.checkColors(PosJCommentSingle.line, PosJCommentSingle.column, 28,
            this.jmlColors, "Color did not Match JMLCommentColor");
   }

   @Test
   public void changeJavaDocToJMLMLineTest() {
      this.removeText(new Position(PosJDocComment.line,
            PosJDocComment.column + 2), 1);
      editor.insertText(PosJDocComment.line, PosJDocComment.column + 2,
            "@");
      this.checkColors(PosJDocComment.line, PosJDocComment.column, 45,
            this.jmlColors, "Color did not Match JMLCommentColor");
   }

   @Test
   public void changeJMLMLineToJavaDocTest() {
      this.removeText(new Position(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2), 1);
      editor.insertText(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2, "*");
      this.checkColors(PosJMLCommentMulti.line, PosJMLCommentMulti.column, 33,
            this.javaDocRGB, "Color did not Match JavaDocColor");
   }

   @Test
   public void changeJavaMLineToJavaDocTest() {
      editor.insertText(PosJCommentMulti.line,
            PosJCommentMulti.column + 2, "*");
      this.checkColors(PosJCommentMulti.line, PosJCommentMulti.column, 29,
            this.javaDocRGB, "Color did not Match JavaDocColor");
   }

   @Test
   public void changeJavaDocToJavaMLineTest() {
      this.removeText(new Position(PosJDocComment.line,
            PosJDocComment.column + 2), 1);
      this.checkColors(PosJDocComment.line, PosJDocComment.column, 44,
            this.javaCommentRGB, "Color did not Match JavaCommentColor");
   }

   @Test
   public void keyWordTestBeforeChanges() {
      this.checkColors(PublicJavaComment.line, PublicJavaComment.column + 2, 6,
            this.javaCommentRGB, "Color did not Match JavaCommentColor");

      this.checkColors(PublicJavaDoc.line, PublicJavaDoc.column + 3, 6,
            this.javaDocRGB, "Color did not Match JavaDocColor");

      this.checkColors(PublicJML.line, PublicJML.column + 3, 6, this.jmlColors,
            "Color did not Match JMLCommentColor");

      this.checkColors(PublicKeyword.line, PublicKeyword.column, 6,
            this.specialWordRGB,
            "Color did not Match color for the \"public\" Java Keyword");
   }

   @Test
   public void keyWordTestAfterChanges() {

      editor.insertText(PublicJavaComment.line,
            PublicJavaComment.column + 2, "@");
      this.checkColors(PublicJavaComment.line, PublicJavaComment.column + 3, 6,
            this.jmlColors, "Color did not Match JMLColor");

      this.removeText(
            new Position(PublicJavaDoc.line, PublicJavaDoc.column + 2), 1);
      editor.insertText(PublicJavaDoc.line, PublicJavaDoc.column + 2, "@");
      this.checkColors(PublicJavaDoc.line, PublicJavaDoc.column + 3, 6,
            this.jmlColors, "Color did not Match JMLColor");
      this.removeText(
            new Position(PublicJavaDoc.line, PublicJavaDoc.column + 2), 1);
      editor.insertText(PublicJavaDoc.line, PublicJavaDoc.column + 2, "*");

      this.removeText(new Position(PublicJML.line, PublicJML.column + 2), 1);
      this.checkColors(PublicJML.line, PublicJML.column + 2, 6,
            this.javaCommentRGB, "Color did not Match JavaCommentColor");
      editor.insertText(PublicJML.line, PublicJML.column + 2, "@");

      this.checkColors(PublicKeyword.line, PublicKeyword.column, 6,
            this.specialWordRGB,
            "Color did not Match color for the \"public\" Java Keyword");
   }

   /*
    * Shortcut for checkColors with a single color
    */
   private void checkColors(final int line, final int column, final int length,
         final RGB color, final String message) {
      this.checkColors(line, column, length, Collections.singleton(color),
            message);
   }

   /**
    * This Method matches the Textcolor of a given piece of code
    *
    * @param line
    *           The line from where to start matching
    * @param column
    *           the column from where to start matching
    * @param length
    *           the length of text that should be matched
    * @param color
    *           all allowed colors
    * @return true if the text starting at line,column with length length has
    *         the given color, else false
    */
   private void checkColors(final int line, final int column, final int length,
         final Set<RGB> colors, final String message) {
      final StyleRange[] textColors = editor.getStyles(line, column,
            length);
      for (final StyleRange r : textColors) {
         assertTrue(message + " at " + r.start + " with length " + r.length,
               colors.contains(r.foreground.getRGB()));

      }
   }

}
