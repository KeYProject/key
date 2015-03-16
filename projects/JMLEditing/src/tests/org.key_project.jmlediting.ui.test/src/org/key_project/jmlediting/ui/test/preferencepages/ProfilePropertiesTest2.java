package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertTrue;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.ui.test.UITestUtils;

public class ProfilePropertiesTest2 {

   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static final String PROJECT_NAME = "TestProperties2";

   private static final List<IJMLProfile> ALL_PROFILES = JMLProfileManagement
         .instance().getAvailableProfilesSortedByName();

   @Test
   public void testShowProjectSpecificProfileAndResetIt() throws CoreException {
      UITestUtils.prepareWorkbench(bot);

      final IProject project = UITestUtils.createEmptyJavaProject(bot,
            PROJECT_NAME);
      final int projectProfileIndex = 0;
      JMLPreferencesHelper.setProjectJMLProfile(project,
            ALL_PROFILES.get(projectProfileIndex));
      final int defaultProfileIndex = ALL_PROFILES.size() - 1;
      JMLPreferencesHelper.setDefaultJMLProfile(ALL_PROFILES
            .get(defaultProfileIndex));

      UITestUtils.openJMLProfileProperties(bot, PROJECT_NAME);

      final SWTBotCheckBox enableProjectSettingsBox = bot.checkBox();
      final SWTBotTable profileList = bot.table();

      bot.sleep(100);

      assertTrue("Enable specific settings checkbox is not checked",
            enableProjectSettingsBox.isChecked());
      UITestUtils.validateProfileListSelection(
            ALL_PROFILES.get(projectProfileIndex), profileList);

      enableProjectSettingsBox.deselect();

      bot.button("Apply").click();

      bot.sleep(100);

      assertTrue("List is enabled when project specific settings are disabled",
            !profileList.isEnabled());
      UITestUtils.validateProfileListSelection(
            JMLPreferencesHelper.getDefaultJMLProfile(), profileList);

      bot.button("Cancel").click();

   }

}
