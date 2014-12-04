package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.junit.Test;
import org.key_project.jmlediting.ui.preferencepages.JMLColorPropertyPreferencePage;
import org.key_project.jmlediting.ui.test.TestUtils;
import org.key_project.jmlediting.ui.util.JML_UIPreferencesHelper;

public class TestJMLColorPropertyPreferencePage {

   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static final String PROJECT_NAME = "TestColorProperties";

   @Test
   public void testProperties() {

      TestUtils.prepareWorkbench(bot);
      final IProject project = TestUtils.createEmptyJavaProject(bot,
            PROJECT_NAME);
      // Open the JML properties page for the project

      bot.tree().getTreeItem(PROJECT_NAME).contextMenu("Properties").click();

      bot.sleep(100);

      bot.tree().getTreeItem("JML").select();
      bot.tree().getTreeItem("JML").expand().getNode("Color").select();

      final SWTBotCheckBox enableProjectSettingsBox = bot.checkBox();
      final SWTBotButton commentColor = bot.buttonWithId(
            JMLColorPropertyPreferencePage.TEST_KEY, "CommentColor");

      bot.sleep(100);
      // Now we are in a color properties page
      // Because this project is null, we require that there are no project
      // specific settings
      assertTrue("Project specific settings enabled on a new project",
            !enableProjectSettingsBox.isChecked());

      bot.sleep(100);

      // Enable project specific settings
      enableProjectSettingsBox.select();
      assertTrue("Cannot select profiles with project specific settings",
            commentColor.isEnabled());

      // System.out.println("The Name of the Properties Shell is: " +
      // bot.activeShell().getText());
      // Lets select a new color

      // TODO: Select a new Color

      final RGB testColor = new RGB(0, 255, 255);

      Display.getDefault().syncExec(new Runnable() {

         @Override
         public void run() {
            final Object oSelector = commentColor.widget.getData();
            assertTrue(oSelector instanceof ColorSelector);
            final ColorSelector selector = (ColorSelector) oSelector;
            selector.setColorValue(testColor);

         }

      });

      bot.sleep(5000);

      // Apply the properties

      bot.button("Apply").click();

      // Now check that this is ok

      final RGB color = JML_UIPreferencesHelper.getProjectJMLColor(project);

      assertEquals("Got wrong project color", testColor, color);

      // Reset Defaults
      bot.button("Restore Defaults").click();

      assertTrue("Project specific settings enabled on a new project",
            !enableProjectSettingsBox.isChecked());

      bot.button("OK").click();
      /*
       * try { String color =
       * project.getPersistentProperty(JMLColorPropertyPreferencePage
       * .COMMENT_COLOR); assertTrue("The Color is not the Default Color",
       * color.
       * equals(JMLColorPropertyPreferencePage.DEFAULT_JML_COMMENT_COLOR.toString
       * ())); System.out.println("The Default Color is ok"); } catch
       * (CoreException e) {
       *
       * }
       */

   }

}
