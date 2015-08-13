package org.key_project.jmlediting.ui.test.Outline;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.runtime.CoreException;
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

   private static final String PROJECT_NAME = "OutlineTest";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "OutlineUpdateTest";
  
   private static String textToAdd = "//@ invariant test;";
   
//   private static String textToAdd2 = "/*@ behavior\r\n     @ requires 1+1;\r\n     @*/\r\n   /**\r\n    * javadoc\r\n    */\r\n";
   
   private static SWTBotTree tree;
   
   
   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();
      TestUtilsUtil.findView(IPageLayout.ID_OUTLINE);
      testProject = JMLEditingUITestUtils.createProjectWithFile(bot, PROJECT_NAME, PACKAGE_NAME, CLASS_NAME, SaveGuarantee.NO_SAVE);

      JMLPreferencesHelper.setProjectJMLProfile(testProject.getProject().getProject(), JMLEditingUITestUtils.findReferenceProfile());
      
      testProject.restoreClassAndOpen();
      editor = testProject.getOpenedEditor();
      
      SWTBotView view = bot.viewByTitle("Outline");
       bot.menu("Window").click().menu("Show View").click().menu("Outline").click();
       view.show();
       tree = view.bot().tree();
       
   }
   
   public void test(String itemSource, String itemName, int it1, int it2) {
      int i = 0;
      for (SWTBotTreeItem item : tree.getAllItems()) {
         //check the invariants
         if(it1 == i++ && item.getItems() != null) {
            int i2 = 0;
            for (SWTBotTreeItem item2: item.getItems()) {
               if(it2 == i2++) {
                  item2.expand();
                  item2.click();
                  item2.select().click();
                  if (item2.getText().equals(itemName)) {
                     assertEquals(itemSource, editor.getSelection());
                     assertEquals(itemName, item2.getText());
                  } else {
                     assertTrue(false);
                  }
                  // assertion gefunden 
                  return;
               }
            }
         }
      }assertTrue("Failed at : " +itemName , false);
   }
   
   
   @AfterClass
   public static void closeEditor() {
      editor.close();
   }

   
   public void saveUpdate() {
      bot.saveAllEditors();
   }
   
   public void addTextSeriell(int startLine, int startCol, String text) {
      for (int i = 0; i < text.length(); i++ ){
//         bot.activeEditor().toTextEditor().insertText(startLine, i+startCol, text.charAt(i));
      }
   }
   
   @Test
   public void outlineUpdateTestOnInitialChange(){
      bot.activeEditor().toTextEditor().insertText(5, 0, textToAdd);
      //TODO: noch saven bzw sollte angezeigt werden da init change !! weitere test kein bock auf den rotz
      test(textToAdd, "invariant test", 1, 0);
   }
   
   public void outlineUpdateTestOnSave() {
 //     bot.activeEditor().toTextEditor().insertText(line, column, text);
   }
   
   
}
