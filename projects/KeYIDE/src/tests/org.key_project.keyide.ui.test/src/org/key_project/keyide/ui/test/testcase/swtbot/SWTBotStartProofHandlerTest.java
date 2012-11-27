package org.key_project.keyide.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.bindings.keys.KeyStroke;
import org.eclipse.jface.bindings.keys.ParseException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.keyboard.Keystrokes;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.keys.KeySequence;
import org.junit.Test;
import org.key_project.keyide.ui.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotStartProofHandlerTest extends TestCase {
   @Test
   public void testSelectionAndOpenedEditor() throws CoreException, InterruptedException, ParseException {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // CLose welcome view
      TestUtilsUtil.closeWelcomeView(bot);
      bot.viewByTitle("CDO Sessions").close();
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotStartProofHandlerTest.testSelectionAndOpenedEditor");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
      // Datei öffnen
      //IEditorPart editorPart = TestUtilsUtil.openEditor(src.getFile("PayCard.java"));
      System.out.println("1111111111111111");
      SWTBotTreeItem item = TestUtilsUtil.selectInProjectExplorer(bot, project.getProject().getName(), "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
      System.out.println("2222222222222222");
//      item.contextMenu("Open").click();
//      item.contextMenu("Start &Proof").click();
//      KeyStroke stroke = KeyStroke.getInstance("M1+M2+P");
//      item.pressShortcut(stroke);
      System.out.println("3333333333333333");
      System.out.println("4444444444444444");
      
      
    //  SWTBotShell dialog = bot.shell("Contract selection");
    //  assertTrue(dialog.bot().list().itemCount() >= 1);
      
      
      
//      SWTBotEditor editor = bot.activeEditor();
//      editor.bot().
   }

}
