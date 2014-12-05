package org.key_project.jmlediting.ui.test.extension;

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
 * <li>null in Comment</li>
 * <li>null in JavaDoc</li>
 * <li>null in Javacode</li>
 * <li>null in JML</li>
 * </ul>
 * after changes:</br>
 * <ul>
 * <li>change from Java SingleLine to JML Single Line</li>
 * <li>change from JML SingleLine to Java SingleLine</li>
 * <li>change from JavaDoc to JML Multiline Comment</li>
 * <li>change from JML Multiline Comment to JavaDoc</li>
 * <li>change from JavaDoc Comment to Java Multiline Comment</li>
 * <li>change from Java Multiline Comment to JavaDoc Comment</li>
 * <li>null in Comment</li>
 * <li>null in JavaDoc</li>
 * <li>null in Javacode</li>
 * <li>null in JML</li>
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
   private static final String CLASS_NAME = "TestClass";

   // SWTBot uses strange offsets... according to JavaClass
   // data/template/TestClass.java
   private static final Position PosOutOfClass = new Position(2, 1);
   private static final Position PosJDocComment = new Position(4, 0);
   private static final Position PosJCommentMulti = new Position(10, 3);
   private static final Position PosJMLCommentMulti = new Position(13, 3);
   private static final Position PosInClass = new Position(16, 3);
   private static final Position PosInString = new Position(20, 25);
   private static final Position PosJCommentSingle = new Position(19, 6);
   private static final Position PosInMethod = new Position(20, 6);
   private static final Position PosJMLCommentSingle = new Position(23, 6);
   private static final Position PosInChar = new Position(24, 14);

   private final RGB singleLineComment = new RGB(63, 127, 95);
   private final RGB multiLineComment = new RGB(63, 127, 95);
   private final RGB javaDoc = new RGB(63, 95, 191);
   private final RGB specialWord = new RGB(127, 0, 85);
   private final RGB defaultText = new RGB(0, 0, 0);
   private final RGB string = new RGB(42, 0, 255);
   private final RGB chararcter = new RGB(42, 0, 255);
   private final RGB jmlComment = new RGB(255, 0, 0);

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
            JMLCommentHighlightingTest.PosJMLCommentSingle.line,
            JMLCommentHighlightingTest.PosJMLCommentSingle.column, 32);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.jmlComment.red
               && r.foreground.getRGB().blue == this.jmlComment.blue
               && r.foreground.getRGB().green == this.jmlComment.green);
      }
   }

   @Test
   public void JMLMultiLineTest() {
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column, 39);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.jmlComment.red
               && r.foreground.getRGB().blue == this.jmlComment.blue
               && r.foreground.getRGB().green == this.jmlComment.green);
      }
   }

   @Test
   public void JavaSingleLineTest() {
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentSingle.line,
            JMLCommentHighlightingTest.PosJCommentSingle.column, 28);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.singleLineComment.red
               && r.foreground.getRGB().blue == this.singleLineComment.blue
               && r.foreground.getRGB().green == this.singleLineComment.green);
      }
   }

   @Test
   public void JavaMultiLineTest() {
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentMulti.line,
            JMLCommentHighlightingTest.PosJCommentMulti.column, 51);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.multiLineComment.red
               && r.foreground.getRGB().blue == this.multiLineComment.blue
               && r.foreground.getRGB().green == this.multiLineComment.green);
      }
   }

   @Test
   public void JavaDocTest() {
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column, 49);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.javaDoc.red
               && r.foreground.getRGB().blue == this.javaDoc.blue
               && r.foreground.getRGB().green == this.javaDoc.green);
      }
   }

   @Test
   public void StringTest() {
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosInString.line,
            JMLCommentHighlightingTest.PosInString.column, 21);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.string.red
               && r.foreground.getRGB().blue == this.string.blue
               && r.foreground.getRGB().green == this.string.green);
         ;
      }
   }

   @Test
   public void JavaCodeTest() {
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosInMethod.line,
            JMLCommentHighlightingTest.PosInMethod.column, 7);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.defaultText.red
               && r.foreground.getRGB().blue == this.defaultText.blue
               && r.foreground.getRGB().green == this.defaultText.green);
      }
   }

   @Test
   public void CharTest() {
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosInChar.line,
            JMLCommentHighlightingTest.PosInChar.column, 3);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.chararcter.red
               && r.foreground.getRGB().blue == this.chararcter.blue
               && r.foreground.getRGB().green == this.chararcter.green);
      }
   }

   @Test
   public void changeJMLMLineToJavaMLineTest() {
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column + 2), 1);
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column, 38);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.multiLineComment.red
               && r.foreground.getRGB().blue == this.multiLineComment.blue
               && r.foreground.getRGB().green == this.multiLineComment.green);
      }
      this.editor.insertText(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2, "@");
   }

   @Test
   public void changeJavaMLineToJMLMLineTest() {
      this.editor.insertText(PosJCommentMulti.line,
            PosJCommentMulti.column + 2, "@");
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentMulti.line,
            JMLCommentHighlightingTest.PosJCommentMulti.column, 52);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.jmlComment.red
               && r.foreground.getRGB().blue == this.jmlComment.blue
               && r.foreground.getRGB().green == this.jmlComment.green);
         this.removeText(new Position(
               JMLCommentHighlightingTest.PosJCommentMulti.line,
               JMLCommentHighlightingTest.PosJCommentMulti.column + 2), 1);

      }
   }

   @Test
   public void changeJMLSLineToJavaSLineTest() {
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJMLCommentSingle.line,
            JMLCommentHighlightingTest.PosJMLCommentSingle.column + 2), 1);
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJMLCommentSingle.line,
            JMLCommentHighlightingTest.PosJMLCommentSingle.column, 31);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.singleLineComment.red
               && r.foreground.getRGB().blue == this.singleLineComment.blue
               && r.foreground.getRGB().green == this.singleLineComment.green);
         this.editor.insertText(PosJMLCommentSingle.line,
               PosJMLCommentSingle.column + 2, "@");
      }
   }

   @Test
   public void changeJavaSLineToJMLSLineTest() {
      this.editor.insertText(PosJCommentSingle.line,
            PosJCommentSingle.column + 2, "@");
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentSingle.line,
            JMLCommentHighlightingTest.PosJCommentSingle.column, 29);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.jmlComment.red
               && r.foreground.getRGB().blue == this.jmlComment.blue
               && r.foreground.getRGB().green == this.jmlComment.green);
      }
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJCommentSingle.line,
            JMLCommentHighlightingTest.PosJCommentSingle.column + 2), 1);
   }

   @Test
   public void changeJavaDocToJMLMLineTest() {
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column + 2), 1);
      this.editor.insertText(PosJDocComment.line, PosJDocComment.column + 2,
            "@");
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column, 39);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.jmlComment.red
               && r.foreground.getRGB().blue == this.jmlComment.blue
               && r.foreground.getRGB().green == this.jmlComment.green);
      }
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column + 2), 1);
      this.editor.insertText(PosJDocComment.line, PosJDocComment.column + 2,
            "*");
   }

   @Test
   public void changeJMLMLineToJavaDocTest() {
      final Boolean test = false;
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column + 2), 1);
      bot.sleep(3000);
      this.editor.insertText(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2, "*");
      bot.sleep(3000);
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column, 49);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.javaDoc.red
               && r.foreground.getRGB().blue == this.javaDoc.blue
               && r.foreground.getRGB().green == this.javaDoc.green);
         /*
          * test = (r.foreground.getRGB().red == this.javaDoc.red &&
          * r.foreground.getRGB().blue == this.javaDoc.blue && r.foreground
          * .getRGB().green == this.javaDoc.green);
          */
      }
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column + 2), 1);
      bot.sleep(3000);
      this.editor.insertText(PosJMLCommentMulti.line,
            PosJMLCommentMulti.column + 2, "@");
      bot.sleep(3000);
      // assertTrue(test);
   }

   @Test
   public void changeJavaMLineToJavaDocTest() {
      this.editor.insertText(PosJCommentMulti.line,
            PosJCommentMulti.column + 2, "*");
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentMulti.line,
            JMLCommentHighlightingTest.PosJCommentMulti.column, 52);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.javaDoc.red
               && r.foreground.getRGB().blue == this.javaDoc.blue
               && r.foreground.getRGB().green == this.javaDoc.green);
      }
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJCommentMulti.line,
            JMLCommentHighlightingTest.PosJCommentMulti.column + 2), 1);
   }

   @Test
   public void changeJavaDocToJavaMLineTest() {
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column + 2), 1);
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column, 48);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getRGB().red == this.multiLineComment.red
               && r.foreground.getRGB().blue == this.multiLineComment.blue
               && r.foreground.getRGB().green == this.multiLineComment.green);
      }
      this.editor.insertText(PosJDocComment.line, PosJDocComment.column + 2,
            "*");
   }

}
