package org.key_project.jmlediting.ui.test.preferencepages;

import static org.eclipse.swtbot.swt.finder.waits.Conditions.waitForMenu;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotList;
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
      SWTBotButton CommentColor = bot.buttonWithTooltip("CommentColor");
      
      
      bot.sleep(100);
      // Now we are in a color properties page
      // Because this project is null, we require that there are no project specific settings
      assertTrue("Project specific settings enabled on a new project", !enableProjectSettingsBox.isChecked());
     
      bot.sleep(100);

      // Enable project specific settings
      enableProjectSettingsBox.select();
      assertTrue("Cannot select profiles with project specific settings", CommentColor.isEnabled());

      bot.sleep(100);
      bot.checkBox("Enable project specific settings").click();      
      // Lets select a new color
      
      //TODO: Select a new Color
      
      CommentColor.click();
      bot.button("OK").click();
     
      
      //Apply Color
      bot.button("Apply").click();
            
      System.out.println(CommentColor.foregroundColor());
      // Apply the properties
      bot.button("OK").click();
      
      // Now check that this is ok

      try {
         String color = project.getPersistentProperty(JMLColorPropertyPreferencePage.COMMENT_COLOR);
         assertTrue("Selected Wrong Color", color.equals(JMLColorPropertyPreferencePage.DEFAULT_JML_COMMENT_COLOR.toString()));
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
      }
      catch (CoreException e) {

      }
     
      
     

      
      
      
      
      
      
   }
   



}
