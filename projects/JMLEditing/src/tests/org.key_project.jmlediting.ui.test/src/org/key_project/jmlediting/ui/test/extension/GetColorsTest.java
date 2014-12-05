package org.key_project.jmlediting.ui.test.extension;

import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.Activator;
import org.key_project.jmlediting.ui.test.TestUtils;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class GetColorsTest {

   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private SWTBotEclipseEditor editor = null;

   private static final String PROJECT_NAME = "TestCompletion";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "TestClass";

   // SWTBot uses strange offsets... according to JavaClass
   // data/template/TestClass.java
   private static final Position PosOutOfClass = new Position(3, 0);
   private static final Position PosJDocComment = new Position(4, 0);
   private static final Position PosJCommentMulti = new Position(10, 3);
   private static final Position PosJMLCommentMulti = new Position(13, 3);
   private static final Position PosInClass = new Position(16, 3);
   private static final Position PosInString = new Position(20, 26);
   private static final Position PosJCommentSingle = new Position(19, 6);
   private static final Position PosInMethod = new Position(20, 6);
   private static final Position PosJMLCommentSingle = new Position(23, 6);
   private static final Position PosInChar = new Position(24, 14);

   /*
    * Initialize a new Project and load the template class from data/template
    * with all kinds of Comments to test AutoCompletion in and open it.
    */
   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      bot.sleep(2000);
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
    * just make sure the global variable editor is set and setting the Colors
    * for Testing
    */
   @Before
   public void initEditor() {
      this.editor = bot.activeEditor().toTextEditor();
   }

   @Test
   public void getcolors() {
      StyleRange color;
      color = this.editor.getStyle(PosJDocComment.line,
            PosJDocComment.column + 1);
      System.out.println("JavaDoc: R= " + color.foreground.getRGB().red
            + " G= " + color.foreground.getRGB().green + " B "
            + color.foreground.getRGB().blue);
      color = this.editor.getStyle(PosJCommentMulti.line,
            PosJCommentMulti.column + 1);
      System.out.println("JCommentMulti: R= " + color.foreground.getRGB().red
            + " G= " + color.foreground.getRGB().green + " B "
            + color.foreground.getRGB().blue);
      color = this.editor.getStyle(PosJCommentSingle.line,
            PosJCommentSingle.column + 1);
      System.out.println("JCommentSingle: R= " + color.foreground.getRGB().red
            + " G= " + color.foreground.getRGB().green + " B "
            + color.foreground.getRGB().blue);
      color = this.editor.getStyle(PosInMethod.line, PosInMethod.column + 1);
      System.out.println("InMethod: R= " + color.foreground.getRGB().red
            + " G= " + color.foreground.getRGB().green + " B "
            + color.foreground.getRGB().blue);
      color = this.editor.getStyle(PosInString.line, PosInString.column + 1);
      System.out.println("InString: R= " + color.foreground.getRGB().red
            + " G= " + color.foreground.getRGB().green + " B "
            + color.foreground.getRGB().blue);
      color = this.editor.getStyle(PosInChar.line, PosInChar.column + 1);
      System.out.println("InChar: R= " + color.foreground.getRGB().red + " G= "
            + color.foreground.getRGB().green + " B "
            + color.foreground.getRGB().blue);
      color = this.editor.getStyle(9, 1);
      System.out.println("Keyword: R= " + color.foreground.getRGB().red
            + " G= " + color.foreground.getRGB().green + " B "
            + color.foreground.getRGB().blue);

      assertTrue(true);
   }
}