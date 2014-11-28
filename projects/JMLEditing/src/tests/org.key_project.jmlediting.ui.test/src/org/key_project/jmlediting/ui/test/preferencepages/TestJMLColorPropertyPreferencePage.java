package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.junit.Test;
import org.key_project.jmlediting.ui.preferencepages.JMLColorPropertyPreferencePage;
import org.key_project.jmlediting.ui.test.TestUtils;

public class TestJMLColorPropertyPreferencePage {

   
   static SWTWorkbenchBot bot= new SWTWorkbenchBot();
   
   private static final String PROJECT_NAME = "TestColorProperties";
   
   
   
   @Test
   public void testProperties() {
      
      TestUtils.prepareWorkbench(bot);
      IProject project = TestUtils.createEmptyJavaProject(bot,PROJECT_NAME);
      //Open the JML properties page for the project
      
      bot.tree().getTreeItem(PROJECT_NAME).contextMenu("Properties").click(); 
      
      bot.sleep(100);
   
      bot.tree().getTreeItem("JML").select();
      bot.tree().getTreeItem("JML").expand().getNode("Color").select();
      
      SWTBotCheckBox enableProjectSettingsBox = bot.checkBox();
      SWTBotButton CommentColor = bot.buttonWithId(JMLColorPropertyPreferencePage.TEST_KEY, "CommentColor");
      
      
      bot.sleep(100);
      // Now we are in a color properties page
      // Because this project is null, we require that there are no project specific settings
      assertTrue("Project specific settings enabled on a new project", !enableProjectSettingsBox.isChecked());
     
      bot.sleep(100);

      // Enable project specific settings
      enableProjectSettingsBox.select();
      assertTrue("Cannot select profiles with project specific settings", CommentColor.isEnabled());

      //System.out.println("The Name of the Properties Shell is: " + bot.activeShell().getText());
      // Lets select a new color
      
      //TODO: Select a new Color
      
      /*
      bot.sleep(1000);
      //CommentColor.click();
     // bot.sleep(1000);
      
      //SWTBotShell colorShell = bot.activeShell();
      
     // System.out.println("The Name of the Color Shell is: " + colorShell.getText());
      
      //System.out.println("The ID of a Button is: " + colorShell.bot().button().getId());
      //System.out.println("The ID of another Button is: " + colorShell.bot().button().getId());
      
     // bot.activeShell();
      bot.sleep(1000);
      bot.button("OK").click();
     // bot.waitUntil(shellCloses(colorShell));
      
      bot.sleep(1000);
            */
      
      // Apply the properties
      
      bot.button("Apply").click();
      
      // Now check that this is ok

      try {
         String color = project.getPersistentProperty(JMLColorPropertyPreferencePage.COMMENT_COLOR);
         assertTrue("Selected Wrong Color", color.equals(JMLColorPropertyPreferencePage.DEFAULT_JML_COMMENT_COLOR.toString()));
         System.out.println("Selected Right Color");
      }
      catch (CoreException e) {

      }
      
      
      
      // Reset Defaults
      bot.button("Restore Defaults").click();
      
      assertTrue("Project specific settings enabled on a new project", !enableProjectSettingsBox.isChecked());
      
      bot.button("OK").click();
      
      try {
         String color = project.getPersistentProperty(JMLColorPropertyPreferencePage.COMMENT_COLOR);
         assertTrue("The Color is not the Default Color", color.equals(JMLColorPropertyPreferencePage.DEFAULT_JML_COMMENT_COLOR.toString()));
         System.out.println("The Default Color is ok");
      }
      catch (CoreException e) {

      }
     
      
     

      
      
      
      
      
      
   }
   



}
