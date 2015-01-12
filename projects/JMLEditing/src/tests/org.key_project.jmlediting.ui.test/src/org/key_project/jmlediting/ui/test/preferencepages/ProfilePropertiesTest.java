package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertTrue;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotList;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.ui.test.UITestUtils;

public class ProfilePropertiesTest {

   static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   
   private static final String PROJECT_NAME = "TestProperties";
   
   private static final List<IJMLProfile> ALL_PROFILES = JMLProfileManagement.getAvailableProfilesSortedByName();
   
   @Test
   public void testBasics() {
       
      UITestUtils.prepareWorkbench(bot);
      
      IProject project = UITestUtils.createEmptyJavaProject(bot,PROJECT_NAME);
      
      
      
      
      // Set the first one as global default
      int gloablDefaultIndex = 0;
      IJMLProfile globalDefault = ALL_PROFILES.get(gloablDefaultIndex);
      JMLPreferencesHelper.setDefaultJMLProfile(globalDefault);
      
      
      //Open the JML properties page for the project
      UITestUtils.openJMLProfileProperties(bot,PROJECT_NAME);
      
      SWTBotCheckBox enableProjectSettingsBox = bot.checkBox();
      SWTBotTable profileList = bot.table();
      
      // Now we are in a profile properties page
      // Because this project is null, we require that there are no project specific settings
      assertTrue("Project specific settings enabled on a new project", !enableProjectSettingsBox.isChecked());
      assertTrue("Can select profiles without project specific settings", !profileList.isEnabled());
      
      // Check that all profiles are shown to the user
      String[] items = new String[profileList.rowCount()];
      for (int i = 0; i < profileList.rowCount(); i++) {
         items[i] = profileList.getTableItem(i).getText(0);
      }
      assertTrue("List of profiles does not contain all profiles", items.length == ALL_PROFILES.size());
      for (int i = 0; i < ALL_PROFILES.size(); i++) {
         assertTrue("List does not contain profiles in sorted order", items[i].equals(ALL_PROFILES.get(i).getName()));
      }
      
      // Enable project specific settings
      enableProjectSettingsBox.select();
      assertTrue("Cannot select profiles with project specific settings", profileList.isEnabled());
      
      UITestUtils.validateProfileListSelection(globalDefault, profileList);
      
      // Lets select a new one
      int newIndex = ALL_PROFILES.size() -1;
      profileList.getTableItem(newIndex).check();
      
      bot.sleep(500);
      
      // Apply the properties
      bot.button("OK").click();
      
      // Now check that this is ok
      IJMLProfile projectProfile = JMLPreferencesHelper.getProjectJMLProfile(project);
      assertTrue("Project profile not changed properly", projectProfile ==ALL_PROFILES.get(newIndex));
      
      
    
      
     
   }

}
