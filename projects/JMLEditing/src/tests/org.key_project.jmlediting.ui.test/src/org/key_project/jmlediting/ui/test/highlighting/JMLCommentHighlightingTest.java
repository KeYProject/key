package org.key_project.jmlediting.ui.test.highlighting;

import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.RGB;
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
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.util.eclipse.BundleUtil;
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
public class JMLCommentHighlightingTest {

   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private SWTBotEclipseEditor editor = null;

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
   private final RGB chararcter = new RGB(42, 0, 255);
   private final RGB jmlComment = JMLUiPreferencesHelper.getDefaultJMLColor();

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
   private void removeText(final Position pos, final int length) {
      this.editor.selectRange(pos.line, pos.column, length);
      bot.sleep(100);
      this.editor.pressShortcut(Keystrokes.DELETE);
   }

   @Test
   public void JMLSingleLineTest() {
      assertTrue("Color did not Match JMLCommentColor", this.checkColors(
            PosJMLCommentSingle.line, PosJMLCommentSingle.column, 30,
            this.jmlComment));
   }

   @Test
   public void JMLMultiLineTest() {
      assertTrue("Color did not Match JMLCommentColor", this.checkColors(
            PosJMLCommentMulti.line, PosJMLCommentMulti.column, 39,
            this.jmlComment));
   }

   @Test
   public void JavaSingleLineTest() {
      assertTrue("Color did not Match JavaCommentColor", this.checkColors(
            PosJCommentSingle.line, PosJCommentSingle.column, 27,
            this.javaCommentRGB));
   }

   @Test
   public void JavaMultiLineTest() {
      assertTrue("Color did not Match JavaCommentColor", this.checkColors(
            PosJCommentMulti.line, PosJCommentMulti.column, 49,
            this.javaCommentRGB));
   }

   @Test
   public void JavaDocTest() {
      assertTrue("Color did not Match JavaDocColor", this.checkColors(
            PosJDocComment.line, PosJDocComment.column, 45, this.javaDocRGB));
   }

   @Test
   public void StringTest() {
      assertTrue("Color did not Match String Color", this.checkColors(
            PosInString.line, PosInString.column, 21, this.string));
   }

   @Test
   public void JavaCodeTest() {
      assertTrue("Color did not Match default Color", this.checkColors(
            PosInMethod.line, PosInMethod.column, 7, this.defaultTextRGB));
   }

   @Test
   public void CharTest() {
      assertTrue("Color did not Match CharColor", this.checkColors(
            PosInChar.line, PosInChar.column, 3, this.chararcter));
   }

   @Test
   public void changeJMLMLineToJavaMLineTest() {
      this.removeText(new Position(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2), 1);
      assertTrue("Color did not Match JavaCommentColor", this.checkColors(
            PosJMLCommentMulti.line, PosJMLCommentMulti.column, 38,
            this.javaCommentRGB));
      this.editor.insertText(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2, "@");
   }

   @Test
   public void changeJavaMLineToJMLMLineTest() {
      this.editor.insertText(PosJCommentMulti.line,
            PosJCommentMulti.column + 2, "@");
      assertTrue("Color did not Match JMLCommentColor",
            this.checkColors(PosJCommentMulti.line, PosJCommentMulti.column,
                  50, this.jmlComment));
      this.removeText(new Position(PosJCommentMulti.line,
            PosJCommentMulti.column + 2), 1);
   }

   @Test
   public void changeJMLSLineToJavaSLineTest() {
      this.removeText(new Position(PosJMLCommentSingle.line,
            PosJMLCommentSingle.column + 2), 1);
      assertTrue("Color did not Match JavaCommentColor", this.checkColors(
            PosJMLCommentSingle.line, PosJMLCommentSingle.column, 29,
            this.javaCommentRGB));
      this.editor.insertText(PosJMLCommentSingle.line,
            PosJMLCommentSingle.column + 2, "@");
   }

   @Test
   public void changeJavaSLineToJMLSLineTest() {
      this.editor.insertText(PosJCommentSingle.line,
            PosJCommentSingle.column + 2, "@");
      assertTrue("Color did not Match JMLCommentColor", this.checkColors(
            PosJCommentSingle.line, PosJCommentSingle.column, 28,
            this.jmlComment));
      this.removeText(new Position(PosJCommentSingle.line,
            PosJCommentSingle.column + 2), 1);
   }

   @Test
   public void changeJavaDocToJMLMLineTest() {
      this.removeText(new Position(PosJDocComment.line,
            PosJDocComment.column + 2), 1);
      this.editor.insertText(PosJDocComment.line, PosJDocComment.column + 2,
            "@");
      assertTrue("Color did not Match JMLCommentColor", this.checkColors(
            PosJDocComment.line, PosJDocComment.column, 45, this.jmlComment));
      this.removeText(new Position(PosJDocComment.line,
            PosJDocComment.column + 2), 1);
      this.editor.insertText(PosJDocComment.line, PosJDocComment.column + 2,
            "*");
   }

   @Test
   public void changeJMLMLineToJavaDocTest() {
      this.removeText(new Position(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2), 1);
      this.editor.insertText(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2, "*");
      assertTrue("Color did not Match JavaDocColor", this.checkColors(
            PosJMLCommentMulti.line, PosJMLCommentMulti.column, 39,
            this.javaDocRGB));
      this.removeText(new Position(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2), 1);
      this.editor.insertText(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2, "@");
   }

   @Test
   public void changeJavaMLineToJavaDocTest() {
      this.editor.insertText(PosJCommentMulti.line,
            PosJCommentMulti.column + 2, "*");
      assertTrue("Color did not Match JavaDocColor",
            this.checkColors(PosJCommentMulti.line, PosJCommentMulti.column,
                  52, this.javaDocRGB));
      this.removeText(new Position(PosJCommentMulti.line,
            PosJCommentMulti.column + 2), 1);
   }

   @Test
   public void changeJavaDocToJavaMLineTest() {
      this.removeText(new Position(PosJDocComment.line,
            PosJDocComment.column + 2), 1);
      assertTrue("Color did not Match JavaCommentColor",
            this.checkColors(PosJDocComment.line, PosJDocComment.column, 44,
                  this.javaCommentRGB));
      this.editor.insertText(PosJDocComment.line, PosJDocComment.column + 2,
            "*");
   }

   @Test
   public void keyWordTestBeforeChanges() {
      assertTrue("Color did not Match JavaCommentColor", this.checkColors(
            PublicJavaComment.line, PublicJavaComment.column + 2, 6,
            this.javaCommentRGB));

      assertTrue("Color did not Match JavaDocColor", this.checkColors(
            PublicJavaDoc.line, PublicJavaDoc.column + 3, 6, this.javaDocRGB));

      assertTrue("Color did not Match JMLCommentColor", this.checkColors(
            PublicJML.line, PublicJML.column + 3, 6, this.jmlComment));

      assertTrue("Color did not Match color for the \"public\" Java Keyword",
            this.checkColors(PublicKeyword.line, PublicKeyword.column, 6,
                  this.specialWordRGB));
   }

   @Test
   public void keyWordTestAfterChanges() {

      this.editor.insertText(PublicJavaComment.line,
            PublicJavaComment.column + 2, "@");
      assertTrue("Color did not Match JMLColor", this.checkColors(
            PublicJavaComment.line, PublicJavaComment.column + 3, 6,
            this.jmlComment));
      this.removeText(new Position(PublicJavaComment.line,
            PublicJavaComment.column + 2), 1);

      this.removeText(
            new Position(PublicJavaDoc.line, PublicJavaDoc.column + 2), 1);
      this.editor.insertText(PublicJavaDoc.line, PublicJavaDoc.column + 2, "@");
      assertTrue("Color did not Match JMLColor", this.checkColors(
            PublicJavaDoc.line, PublicJavaDoc.column + 3, 6, this.jmlComment));
      this.removeText(
            new Position(PublicJavaDoc.line, PublicJavaDoc.column + 2), 1);
      this.editor.insertText(PublicJavaDoc.line, PublicJavaDoc.column + 2, "*");

      this.removeText(new Position(PublicJML.line, PublicJML.column + 2), 1);
      assertTrue("Color did not Match JavaCommentColor", this.checkColors(
            PublicJML.line, PublicJML.column + 2, 6, this.javaCommentRGB));
      this.editor.insertText(PublicJML.line, PublicJML.column + 2, "@");

      assertTrue("Color did not Match color for the \"public\" Java Keyword",
            this.checkColors(PublicKeyword.line, PublicKeyword.column, 6,
                  this.specialWordRGB));
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
    *           the color the text should be
    * @return true if the text starting at line,column with length length has
    *         the given color, else false
    */
   private boolean checkColors(final int line, final int column,
         final int length, final RGB color) {
      boolean matched = true;
      final StyleRange[] textColors = this.editor.getStyles(line, column,
            length);
      for (final StyleRange r : textColors) {
         matched &= r.foreground.getRGB().equals(color);
      }
      return matched;
   }

}
