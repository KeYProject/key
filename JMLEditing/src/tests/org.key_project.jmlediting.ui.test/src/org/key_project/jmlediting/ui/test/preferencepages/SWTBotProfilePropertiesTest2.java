package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotProfilePropertiesTest2 {
   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static final String PROJECT_NAME = "TestProperties2";

   private static final List<IJMLProfile> ALL_PROFILES = JMLProfileManagement.instance().getAvailableProfilesSortedByName();

   @Test
   public void testShowProjectSpecificProfileAndResetIt() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();

      final IProject project = TestUtilsUtil.createJavaProject(PROJECT_NAME).getProject();
      final int projectProfileIndex = 0;
      JMLPreferencesHelper.setProjectJMLProfile(project, ALL_PROFILES.get(projectProfileIndex));
      final int defaultProfileIndex = ALL_PROFILES.size() - 1;
      JMLPreferencesHelper.setDefaultJMLProfile(ALL_PROFILES.get(defaultProfileIndex));

      SWTBotShell propertiesShell = JMLEditingUITestUtils.openJMLProfileProperties(bot, project);

      final SWTBotCheckBox enableProjectSettingsBox = propertiesShell.bot().checkBox();
      final SWTBotTable profileList = propertiesShell.bot().table();

      assertTrue("Enable specific settings checkbox is not checked", enableProjectSettingsBox.isChecked());
      JMLEditingUITestUtils.validateProfileListSelection(ALL_PROFILES.get(projectProfileIndex), profileList);

      enableProjectSettingsBox.deselect();

      propertiesShell.bot().button("Apply").click();

      // Want to do rebuild
      SWTBotShell confirmShell = propertiesShell.bot().shell("Active JML Profile Changed");
      confirmShell.bot().button(IDialogConstants.YES_LABEL).click();

      assertTrue("List is enabled when project specific settings are disabled", !profileList.isEnabled());
      assertEquals(JMLPreferencesHelper.getDefaultJMLProfile(), JMLPreferencesHelper.getProjectActiveJMLProfile(project));
      JMLEditingUITestUtils.validateProfileListSelection(ALL_PROFILES.get(projectProfileIndex), profileList);

      propertiesShell.bot().button(IDialogConstants.CANCEL_LABEL).click();
   }
}
