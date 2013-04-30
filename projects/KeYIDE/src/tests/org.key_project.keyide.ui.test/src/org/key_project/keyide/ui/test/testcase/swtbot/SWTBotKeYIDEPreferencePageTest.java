package org.key_project.keyide.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.keyide.ui.util.KeYIDEPreferences;
import org.key_project.util.test.util.TestUtilsUtil;


public class SWTBotKeYIDEPreferencePageTest extends TestCase {
   
   /**
    * Tests the perspective is always changed functionality by changing the value under "Window->Preferences->General->Perspectives->KeY Preferences"
    * @throws InterruptedException 
    * @throws CoreException 
    */
   @Test
   public void testPerspectiveAlwaysChangedPreferences() throws CoreException, InterruptedException{
      changedPerspectivePreferences("Always");
   }
   

   /**
    * Tests the perspective is never changed functionality by changing the value under "Window->Preferences->General->Perspectives->KeY Preferences"
    * @throws InterruptedException 
    * @throws CoreException 
    */
   @Test
   public void testPerspectiveNeverChangedPreferences() throws CoreException, InterruptedException{
      changedPerspectivePreferences("Never");
   }
   

   /**
    * Tests the switch perspective is set to prompt, by changing the value under "Window->Preferences->General->Perspectives->KeY Preferences"
    * @throws InterruptedException 
    * @throws CoreException 
    */
   @Test
   public void testPerspectivePromptChangedPreferences() throws CoreException, InterruptedException{
      changedPerspectivePreferences("Prompt");
   }
   
   /**
    * Changes the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to the given value.
    * @param radioButton The value to set the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE}.
    * @throws CoreException
    * @throws InterruptedException
    */
   protected void changedPerspectivePreferences(String radioButton) throws CoreException, InterruptedException {
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 4;
      // Backup original switch perspective preference and set preference to test.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT); // TODO: Set it to a value which does not match the value to test. Otherwise you test nothing in case you click on prompt
      // Backup current perspective
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective(); // TODO: Not required, remove this line and later functionality
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      try {
         // Close welcome view if available
         TestUtilsUtil.closeWelcomeView(bot);
         SWTBotShell preferencePage = TestUtilsUtil.openPreferencePage(bot, "General", "Perspectives", "KeY preferences");
         TestUtilsUtil.clickDirectly(preferencePage.bot().radio(radioButton));
         preferencePage.bot().button("OK").click();
         // tests if KeY Preference is set
         assertTrue(radioButton.equalsIgnoreCase(KeYIDEPreferences.getSwitchToKeyPerspective())); // TODO: This is not nice, because maybe we like to change the UI or to support different languages or the eclipse API might change. Instead make sure that the value is one of {@link MessageDialogWithToggle#ALWAYS}, {@link MessageDialogWithToggle#PROMPT} or {@link MessageDialogWithToggle#NEVER}. You can pass the expected value as parameter to this method
      }
      finally {
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }
   
   /**
    * Resets the {@link SWTBotPreferences#TIMEOUT}, the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} and the open perspective.
    * Closes all shells and editors.
    * @param originalTimeout The original {@link SWTBotPreferences#TIMEOUT}.
    * @param originalSwitchPerspectivePreference The original {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE}.
    * @param originalPerspective The original perspective.
    * @param bot
    */
   private void doFinally(long originalTimeout, String originalSwitchPerspectivePreference, IPerspectiveDescriptor originalPerspective, SWTWorkbenchBot bot){
      // Restore original timeout
      SWTBotPreferences.TIMEOUT = originalTimeout;
      // Restore original switch perspective preference.
      KeYIDEPreferences.setSwitchToKeyPerspective(originalSwitchPerspectivePreference);
      // Restore original perspective
      TestUtilsUtil.openPerspective(originalPerspective);
      // close all shells
      bot.closeAllShells();
      // Close all editors
      bot.closeAllEditors();
   }


}
