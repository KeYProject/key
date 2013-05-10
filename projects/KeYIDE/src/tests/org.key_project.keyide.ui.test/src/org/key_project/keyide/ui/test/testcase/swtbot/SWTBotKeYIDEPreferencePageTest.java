package org.key_project.keyide.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.Test;
import org.key_project.keyide.ui.preference.page.KeYIDEPreferencePage;
import org.key_project.keyide.ui.util.KeYIDEPreferences;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWTBot tests for {@link KeYIDEPreferencePage}.
 * @author Martin Hentschel
 */
public class SWTBotKeYIDEPreferencePageTest extends TestCase {
   /**
    * Tests the perspective is always changed functionality by changing the value under "Window->Preferences->General->Perspectives->KeY Preferences"
    * @throws InterruptedException 
    * @throws CoreException 
    */
   @Test
   public void testPerspectiveAlwaysChangedPreferences() throws CoreException, InterruptedException{
      changedPerspectivePreferences("Always", MessageDialogWithToggle.ALWAYS);
   }
   
   /**
    * Tests the perspective is never changed functionality by changing the value under "Window->Preferences->General->Perspectives->KeY Preferences"
    * @throws InterruptedException 
    * @throws CoreException 
    */
   @Test
   public void testPerspectiveNeverChangedPreferences() throws CoreException, InterruptedException{
      changedPerspectivePreferences("Never", MessageDialogWithToggle.NEVER);
   }
   
   /**
    * Tests the switch perspective is set to prompt, by changing the value under "Window->Preferences->General->Perspectives->KeY Preferences"
    * @throws InterruptedException 
    * @throws CoreException 
    */
   @Test
   public void testPerspectivePromptChangedPreferences() throws CoreException, InterruptedException{
      changedPerspectivePreferences("Prompt", MessageDialogWithToggle.PROMPT);
   }
   
   /**
    * Changes the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to the given value.
    * @param radioButton The value to set the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE}.
    * @param expectedValue the expected value is one of {@link MessageDialogWithToggle#ALWAYS}, {@link MessageDialogWithToggle#PROMPT} or {@link MessageDialogWithToggle#NEVER}
    * @throws CoreException
    * @throws InterruptedException
    */
   protected void changedPerspectivePreferences(String radioButton, String expectedValue) throws CoreException, InterruptedException {
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 4;
      // Backup original switch perspective preference and set preference to test.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      if (radioButton.equalsIgnoreCase(MessageDialogWithToggle.PROMPT)) {
         KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.ALWAYS);   
      }
      else {
         KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
      }
      // Backup current perspective
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      try {
         // Close welcome view if available
         TestUtilsUtil.closeWelcomeView(bot);
         SWTBotShell preferencePage = TestUtilsUtil.openPreferencePage(bot, "General", "Perspectives", "KeY preferences");
         TestUtilsUtil.clickDirectly(preferencePage.bot().radio(radioButton));
         preferencePage.bot().button("OK").click();
         // tests if KeY Preference is set
         assertTrue(expectedValue.equals(KeYIDEPreferences.getSwitchToKeyPerspective()));
      }
      finally {
         // Restore original timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Restore original switch perspective preference.
         KeYIDEPreferences.setSwitchToKeyPerspective(originalSwitchPerspectivePreference);
         // close all shells
         bot.closeAllShells();
         // Close all editors
         bot.closeAllEditors();
      }
   }
}
