package org.key_project.jmlediting.ui.test.highlighting;

import static org.junit.Assert.assertEquals;

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

   private static final String PROJECT_NAME = "TestCompletion";
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
      final StyleRange[] textColors = this.editor.getStyles(
            PosJMLCommentSingle.line, PosJMLCommentSingle.column, 30);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JMLCommentColor",
               r.foreground.getRGB(), this.jmlComment);
      }
   }

   @Test
   public void JMLMultiLineTest() {
      final StyleRange[] textColors = this.editor.getStyles(
            PosJMLCommentMulti.line, PosJMLCommentMulti.column, 39);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JMLCommentColor",
               r.foreground.getRGB(), this.jmlComment);
      }
   }

   @Test
   public void JavaSingleLineTest() {
      final StyleRange[] textColors = this.editor.getStyles(
            PosJCommentSingle.line, PosJCommentSingle.column, 27);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaCommentColor",
               r.foreground.getRGB(), this.javaCommentRGB);
      }
   }

   @Test
   public void JavaMultiLineTest() {
      final StyleRange[] textColors = this.editor.getStyles(
            PosJCommentMulti.line, PosJCommentMulti.column, 51);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaCommentColor",
               r.foreground.getRGB(), this.javaCommentRGB);
      }
   }

   @Test
   public void JavaDocTest() {
      final StyleRange[] textColors = this.editor.getStyles(
            PosJDocComment.line, PosJDocComment.column, 49);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaDocColor",
               r.foreground.getRGB(), this.javaDocRGB);
      }
   }

   @Test
   public void StringTest() {
      final StyleRange[] textColors = this.editor.getStyles(PosInString.line,
            PosInString.column, 21);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match String Color",
               r.foreground.getRGB(), this.string);
      }
   }

   @Test
   public void JavaCodeTest() {
      final StyleRange[] textColors = this.editor.getStyles(PosInMethod.line,
            PosInMethod.column, 7);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match default Color",
               r.foreground.getRGB(), this.defaultTextRGB);
      }
   }

   @Test
   public void CharTest() {
      final StyleRange[] textColors = this.editor.getStyles(PosInChar.line,
            PosInChar.column, 3);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match CharColor", r.foreground.getRGB(),
               this.chararcter);
      }
   }

   @Test
   public void changeJMLMLineToJavaMLineTest() {
      this.removeText(new Position(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2), 1);
      final StyleRange[] textColors = this.editor.getStyles(
            PosJMLCommentMulti.line, PosJMLCommentMulti.column, 38);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaCommentColor",
               r.foreground.getRGB(), this.javaCommentRGB);
      }
      this.editor.insertText(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2, "@");
   }

   @Test
   public void changeJavaMLineToJMLMLineTest() {
      this.editor.insertText(PosJCommentMulti.line,
            PosJCommentMulti.column + 2, "@");
      final StyleRange[] textColors = this.editor.getStyles(
            PosJCommentMulti.line, PosJCommentMulti.column, 52);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JMLCommentColor",
               r.foreground.getRGB(), this.jmlComment);
      }
      this.removeText(new Position(PosJCommentMulti.line,
            PosJCommentMulti.column + 2), 1);
   }

   @Test
   public void changeJMLSLineToJavaSLineTest() {
      this.removeText(new Position(PosJMLCommentSingle.line,
            PosJMLCommentSingle.column + 2), 1);
      final StyleRange[] textColors = this.editor.getStyles(
            PosJMLCommentSingle.line, PosJMLCommentSingle.column, 29);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaCommentColor",
               r.foreground.getRGB(), this.javaCommentRGB);
      }
      this.editor.insertText(PosJMLCommentSingle.line,
            PosJMLCommentSingle.column + 2, "@");
   }

   @Test
   public void changeJavaSLineToJMLSLineTest() {
      this.editor.insertText(PosJCommentSingle.line,
            PosJCommentSingle.column + 2, "@");
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentSingle.line,
            JMLCommentHighlightingTest.PosJCommentSingle.column, 28);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JMLCommentColor",
               r.foreground.getRGB(), this.jmlComment);
      }
      this.removeText(new Position(PosJCommentSingle.line,
            PosJCommentSingle.column + 2), 1);
   }

   @Test
   public void changeJavaDocToJMLMLineTest() {
      this.removeText(new Position(PosJDocComment.line,
            PosJDocComment.column + 2), 1);
      this.editor.insertText(PosJDocComment.line, PosJDocComment.column + 2,
            "@");
      final StyleRange[] textColors = this.editor.getStyles(
            PosJDocComment.line, PosJDocComment.column, 39);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JMLCommentColor",
               r.foreground.getRGB(), this.jmlComment);
      }
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
      final StyleRange[] textColors = this.editor.getStyles(
            PosJMLCommentMulti.line, PosJMLCommentMulti.column, 39);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaDocColor",
               r.foreground.getRGB(), this.javaDocRGB);
      }
      this.removeText(new Position(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2), 1);
      this.editor.insertText(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2, "@");
   }

   @Test
   public void changeJavaMLineToJavaDocTest() {
      this.editor.insertText(PosJCommentMulti.line,
            PosJCommentMulti.column + 2, "*");
      final StyleRange[] textColors = this.editor.getStyles(
            PosJCommentMulti.line, PosJCommentMulti.column, 52);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaDocColor",
               r.foreground.getRGB(), this.javaDocRGB);
      }
      this.removeText(new Position(PosJCommentMulti.line,
            PosJCommentMulti.column + 2), 1);
   }

   @Test
   public void changeJavaDocToJavaMLineTest() {
      this.removeText(new Position(PosJDocComment.line,
            PosJDocComment.column + 2), 1);
      final StyleRange[] textColors = this.editor.getStyles(
            PosJDocComment.line, PosJDocComment.column, 48);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaCommentColor",
               r.foreground.getRGB(), this.javaCommentRGB);
      }
      this.editor.insertText(PosJDocComment.line, PosJDocComment.column + 2,
            "*");
   }

   @Test
   public void keyWordTestBeforeChanges() {
      StyleRange[] textColors = this.editor.getStyles(PublicJavaComment.line,
            PublicJavaComment.column + 2, 6);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaCommentColor",
               r.foreground.getRGB(), this.javaCommentRGB);
      }
      textColors = this.editor.getStyles(PublicJavaDoc.line,
            PublicJavaDoc.column + 2, 6);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaDocColor",
               r.foreground.getRGB(), this.javaDocRGB);
      }
      textColors = this.editor.getStyles(PublicJML.line, PublicJML.column + 2,
            6);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JMLCommentColor",
               r.foreground.getRGB(), this.jmlComment);
      }
      textColors = this.editor.getStyles(PublicKeyword.line,
            PublicKeyword.column, 6);
      for (final StyleRange r : textColors) {
         assertEquals(
               "Color did not Match color for the \"public\" Java Keyword",
               r.foreground.getRGB(), this.specialWordRGB);
      }
   }

   @Test
   public void keyWordTestAfterChanges() {

      this.editor.insertText(PublicJavaComment.line,
            PublicJavaComment.column + 2, "@");
      StyleRange[] textColors = this.editor.getStyles(PublicJavaComment.line,
            PublicJavaComment.column + 2, 6);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JMLColor", r.foreground.getRGB(),
               this.jmlComment);
      }
      this.removeText(new Position(PublicJavaComment.line,
            PublicJavaComment.column + 2), 1);

      this.removeText(
            new Position(PublicJavaDoc.line, PublicJavaDoc.column + 2), 1);
      this.editor.insertText(PublicJavaDoc.line, PublicJavaDoc.column + 2, "@");
      textColors = this.editor.getStyles(PublicJavaDoc.line,
            PublicJavaDoc.column + 3, 6);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JMLColor", r.foreground.getRGB(),
               this.jmlComment);
      }
      this.removeText(
            new Position(PublicJavaDoc.line, PublicJavaDoc.column + 2), 1);
      this.editor.insertText(PublicJavaDoc.line, PublicJavaDoc.column + 2, "*");

      this.removeText(new Position(PublicJML.line, PublicJML.column + 2), 1);
      textColors = this.editor.getStyles(PublicJML.line, PublicJML.column + 2,
            6);
      for (final StyleRange r : textColors) {
         assertEquals("Color did not Match JavaCommentColor",
               r.foreground.getRGB(), this.javaCommentRGB);
      }
      this.editor.insertText(PublicJML.line, PublicJML.column + 2, "@");

      textColors = this.editor.getStyles(PublicKeyword.line,
            PublicKeyword.column, 6);
      for (final StyleRange r : textColors) {
         assertEquals(
               "Color did not Match color for the \"public\" Java Keyword",
               r.foreground.getRGB(), this.specialWordRGB);
      }
   }

}
