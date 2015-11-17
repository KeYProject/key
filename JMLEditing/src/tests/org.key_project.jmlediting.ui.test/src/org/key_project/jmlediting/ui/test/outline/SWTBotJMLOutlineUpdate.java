package org.key_project.jmlediting.ui.test.outline;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPageLayout;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotJMLOutlineUpdate {

   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   private static TestProject testProject;
   private static SWTBotEclipseEditor editor = null;

   private static final String PROJECT_NAME = "OutlineTestUpdate";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "OutlineUpdateTest";

   private static String textToAdd2 = "//@ invariant a < b;";
   private static String textToAddMethod = "\t//@behavior";

   private static SWTBotTree tree;

   @BeforeClass
   public static void initProject() throws Exception {
      TestUtilsUtil.closeWelcomeView();
      TestUtilsUtil.findView(IPageLayout.ID_OUTLINE);
      testProject = JMLEditingUITestUtils.createProjectWithFile(bot, PROJECT_NAME,
               PACKAGE_NAME, CLASS_NAME, SaveGuarantee.NO_SAVE);

      JMLPreferencesHelper.setProjectJMLProfile(testProject.getProject().getProject(),
               JMLEditingUITestUtils.findReferenceProfile());

      testProject.restoreClassAndOpen();
      editor = testProject.getOpenedEditor();

      TestUtilsUtil.openView(IPageLayout.ID_OUTLINE);
      SWTBotView view = bot.viewByTitle("Outline");
      tree = view.bot().tree();
   }

   private int getLine(String s) {
      int i = 0;
      for (String linestr : editor.getLines()) {
         if (linestr.contains(s)) {
            return i;
         }
         else
            i++;
      }
      return -1;
   }

   public void test(String itemSource, String itemName, int it1, int it2) {
      int i = 0;
      for (SWTBotTreeItem item : tree.getAllItems()) {
         // check the invariants
         if (it1 == i++ && item.getItems() != null) {
            int i2 = 0;
            for (SWTBotTreeItem item2 : item.getItems()) {
               if (it2 == i2++) {
                  item2.expand();
                  item2.click();
                  item2.select().click();
                  if (item2.getText().equals(itemName)) {
                     assertEquals(itemSource.trim(), editor.getSelection().trim());
                     assertEquals(itemName, item2.getText());
                  }
                  else {
                     assertTrue(false);
                  }
                  // assertion gefunden
                  return;
               }
            }
         }
      }
      assertTrue("Failed at : " + itemName, false);
   }

   public static void testbehavior(String method, String itemSource, String itemName,
            boolean reloadtree) {
      if (reloadtree) {
         tree = bot.viewByTitle("Outline").bot().tree();
      }
      for (SWTBotTreeItem item : tree.getAllItems()) {
         if (item.getItems() != null) {
            for (SWTBotTreeItem item2 : item.getItems()) {
               if (item2.getText().equals(method)) {
                  item2.expand();
                  item2.getItems()[0].select().click();
                  assertEquals(itemName.trim(), item2.getItems()[0].getText().trim());
                  assertEquals(itemSource.trim(), editor.getSelection().trim());
                  return;
               }
            }
         }
      }
      assertTrue(method + ": No Method Found", false);

   }

   @AfterClass
   public static void closeEditor() {
      editor.close();
   }

   public void addTextSeriell(int startLine, int startCol, String text) {
      for (int i = 0; i < text.length(); i++) {
         bot.activeEditor().toTextEditor()
                  .insertText(startLine, i + startCol, String.valueOf(text.charAt(i)));
      }
      // Give the outline time to update
      bot.sleep(2000);
   }

   @Test
   public void outlineUpdateInvariant() {
      addTextSeriell(6, 0, textToAdd2);
   }

   @Test
   public void outlineUpdateMethod() {
      addTextSeriell(getLine("public void ab") - 1, 0, textToAddMethod);
      testbehavior("ab() : void", "//@behavior", "behavior", true);
   }

   @Test
   public void outlinePureType() {
      addTextSeriell(getLine("public void a"), 9, " /*@pure@*/");
      testbehavior("a() : void", "/*@pure@*/", "pure", true);
   }

   @Test
   public void outlineSpecType() {
      addTextSeriell(getLine("private int i"), 10, "/*@spec_public@*/ ");
      testbehavior("i : int", "/*@spec_public@*/", "spec_public", true);
   }

}
