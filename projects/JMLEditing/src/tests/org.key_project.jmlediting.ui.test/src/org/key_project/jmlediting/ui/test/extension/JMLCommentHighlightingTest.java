package org.key_project.jmlediting.ui.test.extension;

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
 * </ul>
 * after changes:</br>
 * <ul>
 * <li>change from Java SingleLine to JML Single Line</li>
 * <li>change from JML SingleLine to Java SingleLine</li>
 * <li>change from JavaDoc to JML Multiline Comment</li>
 * <li>change from JML Multiline Comment to JavaDoc</li>
 * <li>change from JavaDoc Comment to Java Multiline Comment</li>
 * <li>change from Java Multiline Comment to JavaDoc Comment</li>
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
   private static final Position PosOutOfClass = new Position(3, 0);
   private static final Position PosJDocComment = new Position(5, 0);
   private static final Position PosJCommentMulti = new Position(11, 3);
   private static final Position PosJMLCommentMulti = new Position(14, 3);
   private static final Position PosInClass = new Position(17, 3);
   private static final Position PosInString = new Position(21, 25);
   private static final Position PosJCommentSingle = new Position(20, 6);
   private static final Position PosInMethod = new Position(21, 6);
   private static final Position PosJMLCommentSingle = new Position(24, 6);
   private static final Position PosInChar = new Position(25, 14);

   private int red;
   private int green;
   private int blue;

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
      bot.sleep(1000);
      JMLPreferencesHelper.setProjectJMLProfile(project.getProject(),
            TestUtils.findReferenceProfile());
   }

   /*
    * just make sure the global variable editor is set
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
      this.editor = bot.activeEditor().toTextEditor();
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJMLCommentSingle.line,
            JMLCommentHighlightingTest.PosJMLCommentSingle.column, 30);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void JMLMultiLineTest() {
      this.editor = bot.activeEditor().toTextEditor();
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column, 39);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void JavaSingleLineTest() {
      this.editor = bot.activeEditor().toTextEditor();
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentSingle.line,
            JMLCommentHighlightingTest.PosJCommentSingle.column, 27);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void JavaMultiLineTest() {
      this.editor = bot.activeEditor().toTextEditor();
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentMulti.line,
            JMLCommentHighlightingTest.PosJCommentMulti.column, 49);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void JavaDocTest() {
      this.editor = bot.activeEditor().toTextEditor();
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column, 49);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void StringTest() {
      this.editor = bot.activeEditor().toTextEditor();
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosInString.line,
            JMLCommentHighlightingTest.PosInString.column, 21);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void JavaCodeTest() {
      this.editor = bot.activeEditor().toTextEditor();
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosInMethod.line,
            JMLCommentHighlightingTest.PosInString.column, 7);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void CharTest() {
      this.editor = bot.activeEditor().toTextEditor();
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosInChar.line,
            JMLCommentHighlightingTest.PosInChar.column, 3);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void changeJMLMLineToJavaMLineTest() {
      this.editor = bot.activeEditor().toTextEditor();
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column + 2), 1);
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column, 38);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void changeJavaMLineToJMLMLineTest() {
      this.editor = bot.activeEditor().toTextEditor();
      this.editor.typeText(JMLCommentHighlightingTest.PosJCommentMulti.line,
            JMLCommentHighlightingTest.PosJCommentMulti.column + 2, "@");
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentMulti.line,
            JMLCommentHighlightingTest.PosJCommentMulti.column, 50);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void changeJMLSLineToJavaSLineTest() {
      this.editor = bot.activeEditor().toTextEditor();
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJMLCommentSingle.line,
            JMLCommentHighlightingTest.PosJMLCommentSingle.column + 2), 1);
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJMLCommentSingle.line,
            JMLCommentHighlightingTest.PosJMLCommentSingle.column, 29);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void changeJavaSLineToJMLSLineTest() {
      this.editor = bot.activeEditor().toTextEditor();
      this.editor.typeText(JMLCommentHighlightingTest.PosJCommentSingle.line,
            JMLCommentHighlightingTest.PosJCommentSingle.column + 2, "@");
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentSingle.line,
            JMLCommentHighlightingTest.PosJCommentSingle.column, 28);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void changeJMLMLineToJavaDocTest() {
      this.editor = bot.activeEditor().toTextEditor();
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column + 2), 1);
      this.editor.typeText(JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column + 2, "@");
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJMLCommentMulti.line,
            JMLCommentHighlightingTest.PosJMLCommentMulti.column, 38);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void changeJavaDocToJMLMLineTest() {
      this.editor = bot.activeEditor().toTextEditor();
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column + 2), 1);
      this.editor.typeText(JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column + 2, "*");
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column, 49);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void changeJavaMLineToJavaDocTest() {
      this.editor = bot.activeEditor().toTextEditor();
      this.editor.typeText(JMLCommentHighlightingTest.PosJCommentMulti.line,
            JMLCommentHighlightingTest.PosJCommentMulti.column + 2, "*");
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJCommentMulti.line,
            JMLCommentHighlightingTest.PosJCommentMulti.column, 50);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

   @Test
   public void changeJavaDocToJavaMLineTest() {
      this.editor = bot.activeEditor().toTextEditor();
      this.removeText(new Position(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column + 2), 1);
      // TODO: set Testcolor
      final StyleRange[] textColors = this.editor.getStyles(
            JMLCommentHighlightingTest.PosJDocComment.line,
            JMLCommentHighlightingTest.PosJDocComment.column, 48);
      for (final StyleRange r : textColors) {
         assertTrue(r.foreground.getBlue() == this.blue
               && r.foreground.getRed() == this.red
               && r.foreground.getGreen() == this.green);
      }
   }

}
