package org.key_project.jmlediting.ui.test.outline;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
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

public class SWTBotJMLOutlineSpecPure {

   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   private static TestProject testProject;
   private static SWTBotEclipseEditor editor = null;

   private static final String PROJECT_NAME = "OutlineTestSpecPure";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "OutlineSpecTest";

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

   @AfterClass
   public static void closeEditor() {
      editor.close();
   }

   public static void testChild(String varName, String itemSource, String itemName,
            boolean reloadtree) {
      if (reloadtree) {
         tree = bot.viewByTitle("Outline").bot().tree();
      }
      for (SWTBotTreeItem item : tree.getAllItems()) {
         if (item.getItems() != null) {
            for (SWTBotTreeItem item2 : item.getItems()) {
               if (item2.getText().equals(varName)) {
                  item2.expand();
                  for (SWTBotTreeItem lastitm : item2.getItems())
                     if (lastitm.getText().equals(itemName)) {
                        lastitm.select().click();
                        assertEquals(itemName, lastitm.getText());
                        assertEquals(itemSource, editor.getSelection());
                        return;
                     }
               }
            }
         }

      }
      assertTrue(varName + ": No Method Found", false);

   }

   @Test
   public void TestFieldSingleAnnotation() {
      testChild("balance : int", "/*@ spec_public@*/", "spec_public", false);
   }

   @Test
   public void TestFieldMultipleAnnotation() {
      testChild("balance2 : int", "/*@ spec_protected nullable@*/",
               "spec_protected nullable", false);
   }

   @Test
   public void TestMethodSingle() {
      testChild("amount() : int", "/*@ pure @*/", "pure", false);
   }

   @Test
   public void TestMethodMultiple() {
      testChild("testMulti() : int", "/*@ pure nullable @*/", "pure nullable", false);
   }

   @Test
   public void TestnoChildWithoutJML() {
      for (SWTBotTreeItem item : tree.getAllItems()) {
         if (item.getItems() != null) {
            for (SWTBotTreeItem item2 : item.getItems()) {
               if (item2.getText().equals("a : int")) {
                  assertFalse("Feld hat Kinder", item2.getItems().length != 0);
                  return;
               }
            }
         }

      }
   }

}
