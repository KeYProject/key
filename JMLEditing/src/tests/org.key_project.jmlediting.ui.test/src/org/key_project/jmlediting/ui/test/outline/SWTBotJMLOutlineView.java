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

public class SWTBotJMLOutlineView {

   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   private static TestProject testProject;
   private static SWTBotEclipseEditor editor = null;

   private static final String PROJECT_NAME = "OutlineTestView";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "OutlineTestClass";

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
                  assertEquals(itemName, item2.getItems()[0].getText());
                  assertEquals(itemSource, editor.getSelection());
                  return;
               }
            }
         }

      }
      assertTrue(method + ": No Method Found", false);

   }

   public static void test(String itemSource, String itemName, int it1, int it2) {
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
                     assertEquals(itemSource, editor.getSelection());
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

   @Test
   public void invariantTestClickSelectionMultiLine() {
      test("/*@\r\n   @ invariant 4 = 4;\r\n   @\r\n   @*/", "invariant 4 = 4", 1, 0);
   }

   @Test
   public void invariantTestClickSelectionSingleLine1() {
      test("//@ public invariant 4 = 4;", "public invariant 4 = 4", 1, 1);
   }

   @Test
   public void invariantTestClickSelectionSingleLine2() {
      test("//@ private invariant 4 = 4;", "private invariant 4 = 4", 1, 2);
   }

   @Test
   public void invariantTestClickSelectionSingleLine3() {
      test("//@ protected invariant 4 = 4;", "protected invariant 4 = 4", 1, 3);
   }

   @Test
   public void invariantTestClickSelectionSingleLine4() {
      test("//@invariant 1 == 1;", "invariant 1 == 1", 1, 4);
   }

   @Test
   public void behaviorTest1Normal() {
      testbehavior("a() : void", "/*@ normal_behavior\r\n   @  requires x > y;\r\n   @*/",
               "normal_behavior requires x > y", false);
   }

   @Test
   public void behaviorTest2() {
      testbehavior("ab() : void", "/*@ behavior\r\n   @ requires x > y;\r\n   @*/",
               "behavior requires x > y", false);
   }

   @Test
   public void behaviorTest3Exceptional() {
      testbehavior("acb() : void",
               "/*@ exceptional_behavior\r\n   @ requires x > y;\r\n   @*/",
               "exceptional_behavior requires x > y", false);
   }

   @Test
   public void testGhost() {
      test("//@ ghost int a = 1;", "ghost int a = 1", 1, 5);
   }

   @Test
   public void testSet() {
      test("//@ set a = \"a\";", "set a = \"a\"", 1, 6);
   }

}
