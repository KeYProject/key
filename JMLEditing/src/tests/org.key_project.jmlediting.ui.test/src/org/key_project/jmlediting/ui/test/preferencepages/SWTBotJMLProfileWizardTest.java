package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCombo;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTableItem;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotJMLProfileWizardTest {
   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static final String PROFILE_NAME = "Profile Name:";
   private static final String DERIVED_FROM = "Derived from:";
   private static final String KEYWORDTABLE_VIEW = "Supported Keywords";
   private static final String KEYWORDTABLE_EDIT = "Keywords from parent profile:";
   private static final String DERIVEDTABLE = "Custom Keywords:";
   private static final String PROFILETABLE_LABEL = "Choose active JML Profile from available ones:";

   private static final String NEW_PROFILE_NAME = "TestProfile123";
   private static final String THIRD_NEW_PROFILE_NAME = "ThirdProfile456";
   private static final String SECOND_NEW_PROFILE_NAME = "SecondProfile";
   private static final String PROFILENAME_TO_SELECT = "KeY Profile";

   private static final String PROJECT_NAME = "ProfileDialogTestProject";
   private static final String PROJECT_SETTINGS_LABEL = "Enable project specific settings";

   /**
    * Types to test whether widget is added
    *
    * @author Thomas Glaser
    *
    */
   private enum Type {
      combo, text, table;
   }

   @BeforeClass
   public static void init() {
      TestUtilsUtil.closeWelcomeView();
   }

   private void closeProfileSettings(SWTBotShell preferenceShell, boolean rebuildExpected, Boolean rebuild) {
      boolean preferenceShellShouldBeClosed = true;
      preferenceShell.bot().button(IDialogConstants.OK_LABEL).click();
      boolean buildTriggered = false;
      if (rebuildExpected) {
         SWTBotShell shell = preferenceShell.bot().shell("Active JML Profile Changed");
         if (rebuild == null) {
            shell.bot().button(IDialogConstants.CANCEL_LABEL).click();
            preferenceShellShouldBeClosed = false;
         }
         else if (rebuild) {
            shell.bot().button(IDialogConstants.YES_LABEL).click();
            buildTriggered = true;
         }
         else {
            shell.bot().button(IDialogConstants.NO_LABEL).click();
            buildTriggered = true;
         }
         preferenceShell.bot().waitUntil(Conditions.shellCloses(shell));
      }
      if (preferenceShellShouldBeClosed) {
         preferenceShell.bot().waitUntil(Conditions.shellCloses(preferenceShell));
      }
      else {
         assertTrue(preferenceShell.isOpen());
      }
      if (buildTriggered) {
         TestUtilsUtil.waitForBuild();         
      }
   }

   @Test
   public void testCurrentProfileIsSelected() {
      SWTBotShell preferenceShell = JMLEditingUITestUtils.openJMLProfilePreferencePage(bot);
      final String selectedProfileName = this.getCheckedItemFirstColumn(preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL));
      assertEquals("not the right Profile is selected", selectedProfileName, JMLPreferencesHelper.getDefaultJMLProfile().getName());
      closeProfileSettings(preferenceShell, false, false);
   }

   @Test
   public void testOnlyOneItemIsChecked() {
      SWTBotShell preferenceShell = JMLEditingUITestUtils.openJMLProfilePreferencePage(bot);
      final int count = this.getCheckedItemCount(preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL));
      assertEquals("Less or more than 1 Profile is checked!", 1, count);
      closeProfileSettings(preferenceShell, false, false);
   }

   @Test
   public void testNewProfileSelection() {
      SWTBotShell preferenceShell = JMLEditingUITestUtils.openJMLProfilePreferencePage(bot);
      final String currentProfileName = this.getCheckedItemFirstColumn(preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL));
      final SWTBotTableItem newProfileItem = preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL).getTableItem(PROFILENAME_TO_SELECT);
      newProfileItem.check();
      preferenceShell.bot().button("Apply").click();
//      try {
//         bot.button("Yes").click();
//      }
//      catch (final WidgetNotFoundException wnfe) {
//         // when run single no dialog appears, in suite it does...
//      }
      final String selectedProfileName = this.getCheckedItemFirstColumn(preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL));
      assertEquals("The newly checked Profile gets not ", newProfileItem.getText(0), selectedProfileName);
      preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL).getTableItem(currentProfileName).check();
      preferenceShell.bot().button("Apply").click();
//      try {
//         bot.button("Yes").click();
//      }
//      catch (final WidgetNotFoundException wnfe) {
//         // when run single no dialog appears, in suite it does...
//      }
      closeProfileSettings(preferenceShell, false, false);
   }

   @Test
   public void testViewProfile() {
      SWTBotShell preferenceShell = JMLEditingUITestUtils.openJMLProfilePreferencePage(bot);
      final IJMLProfile profile = JMLPreferencesHelper.getDefaultJMLProfile();
      SWTBotTable profileTable = preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL);
      profileTable.select(profile.getName());
      preferenceShell.bot().button("View...").click();
      
      SWTBotShell viewShell = preferenceShell.bot().shell("View Profile");
      final SWTBotText profileNameText = viewShell.bot().textWithLabel(PROFILE_NAME);
      assertFalse(TestUtilsUtil.isEditable(profileNameText));
      assertEquals("Profile Name is not set correct!", profile.getName(), profileNameText.getText());

      final SWTBotTable table = viewShell.bot().tableWithLabel(KEYWORDTABLE_VIEW);
      assertEquals("Not the right amount of keywords is shown", profile.getSupportedKeywords().size(), table.rowCount());

      this.testWidgetNotThere(viewShell.bot(), Type.combo, DERIVED_FROM);
      this.testWidgetNotThere(viewShell.bot(), Type.table, DERIVEDTABLE);
      closeProfileSettings(preferenceShell, false, false);
   }

   /**
    * need this in order, because only a derived profile can be edited, and by
    * default there is no derived profile...
    */
   @Test
   public void testNewAndEditAndDeleteProfile() {
      SWTBotShell preferenceShell = JMLEditingUITestUtils.openJMLProfilePreferencePage(bot);
      this.createNewProfileAndSave(preferenceShell, NEW_PROFILE_NAME);
      this.testEditProfile(preferenceShell);
      this.testDeleteProfile(preferenceShell);
      closeProfileSettings(preferenceShell, false, false);
   }

   @Test
   public void testDeleteUsedProfile() throws CoreException, InterruptedException {
      SWTBotShell preferenceShell = JMLEditingUITestUtils.openJMLProfilePreferencePage(bot);
      this.createNewProfileAndSave(preferenceShell, THIRD_NEW_PROFILE_NAME);
      this.closeProfileSettings(preferenceShell, false, false);

      IJavaProject project = TestUtilsUtil.createJavaProject(PROJECT_NAME);

      SWTBotShell propertiesShell = JMLEditingUITestUtils.openJMLProfileProperties(bot, project.getProject());
      propertiesShell.bot().checkBox(PROJECT_SETTINGS_LABEL).click();

      propertiesShell.bot().tableWithLabel(PROFILETABLE_LABEL).getTableItem(THIRD_NEW_PROFILE_NAME).check();

      closeProfileSettings(propertiesShell, true, true);

      preferenceShell = JMLEditingUITestUtils.openJMLProfilePreferencePage(bot);

      preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL).getTableItem(THIRD_NEW_PROFILE_NAME).select();
      preferenceShell.bot().button("Delete").click();

      SWTBotShell deleteShell = preferenceShell.bot().shell("Cannot delete profile");
      deleteShell.bot().button(IDialogConstants.OK_LABEL).click();
      
      closeProfileSettings(preferenceShell, false, false);
   }

   private void testDeleteProfile(SWTBotShell preferenceShell) {
      final SWTBotTable profileTable = preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL);

      profileTable.getTableItem(PROFILENAME_TO_SELECT).select();
      assertFalse("Delete Button is enabled on KeY Profile!", preferenceShell.bot().button("Delete").isEnabled());

      profileTable.getTableItem(SECOND_NEW_PROFILE_NAME).select();
      preferenceShell.bot().button("Delete").click();

      assertTrue("Delete Profile was not successfull!",
                 !profileTable.containsItem(SECOND_NEW_PROFILE_NAME) && 
                 !profileTable.containsItem(NEW_PROFILE_NAME));
   }

   private void testEditProfile(SWTBotShell preferenceShell) {
      preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL).getTableItem(NEW_PROFILE_NAME).select();
      preferenceShell.bot().button("Edit...").click();

      SWTBotShell editShell = preferenceShell.bot().shell("Edit Profile");
      assertFalse("DerivedFromCombo should be disabled!", editShell.bot().comboBoxWithLabel(DERIVED_FROM).isEnabled());

      final SWTBotTable keywordTable = editShell.bot().tableWithLabel(KEYWORDTABLE_EDIT);

      assertFalse("Disabled Keyword is not saved!", keywordTable.getTableItem(0).isChecked());
      boolean allOtherChecked = true;
      for (int i = 1; i < keywordTable.rowCount(); i++) {
         if (allOtherChecked) {
            allOtherChecked = keywordTable.getTableItem(2).isChecked();
         }
      }
      assertTrue("Too many Keywords are disabled!", allOtherChecked);

      final SWTBotText profileNameText = editShell.bot().textWithLabel(PROFILE_NAME);
      profileNameText.setText(SECOND_NEW_PROFILE_NAME);

      editShell.bot().button(IDialogConstants.OK_LABEL).click();
      editShell.bot().waitUntil(Conditions.shellCloses(editShell));

      assertTrue("Edit Profile was not successfull! (edit name not saved)",
                 preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL).containsItem(SECOND_NEW_PROFILE_NAME) && 
                 !preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL).containsItem(NEW_PROFILE_NAME));
   }

   private void createNewProfileAndSave(final SWTBotShell preferenceShell, final String profileName) {
      preferenceShell.bot().button("New...").click();
      SWTBotShell createProfileShell = preferenceShell.bot().shell("Create Profile");

      // first check
      SWTBotButton okButton = createProfileShell.bot().button(IDialogConstants.OK_LABEL);
      SWTBotText nameText = createProfileShell.bot().textWithLabel(PROFILE_NAME);
      assertFalse(okButton.isEnabled()); // Name not defined
      nameText.setText(profileName);
      assertFalse(okButton.isEnabled()); // Parent profile not defined
      // second check
      nameText.setText("");
      SWTBotCombo profileCombo = createProfileShell.bot().comboBoxWithLabel(DERIVED_FROM);
      profileCombo.setSelection(PROFILENAME_TO_SELECT);
      assertFalse(okButton.isEnabled()); // Name not defined
      nameText.setText(profileName);
      // third check
      assertTrue(okButton.isEnabled());
      // Test shown keywords
      final IJMLProfile selectedProfile = JMLProfileManagement.instance().getProfileFromName(PROFILENAME_TO_SELECT);
      assertNotNull(selectedProfile);
      final SWTBotTable keywordTable = createProfileShell.bot().tableWithLabel(KEYWORDTABLE_EDIT);
      assertEquals("Not the right amount of keywords is shown!",
                   selectedProfile.getSupportedKeywords().size(),
                   keywordTable.rowCount());
      // Uncheck first keyword
      SWTBotTableItem firstItem = keywordTable.getTableItem(0);
      IKeyword keyword = (IKeyword)TestUtilsUtil.getTableItemData(firstItem);
      firstItem.uncheck();
      // Finish profile creation
      TestUtilsUtil.clickDirectly(okButton);
      // Ensure that new profile is shown
      SWTBotTableItem profileItem = preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL).getTableItem(profileName);
      assertNotNull("New Profile is not saved!", profileItem);
      // Test content of created profile
      IEditableDerivedProfile createdProfile = (IEditableDerivedProfile)TestUtilsUtil.getTableItemData(profileItem);
      assertEquals(profileName, createdProfile.getName());
      assertEquals(selectedProfile, createdProfile.getParentProfile());
      assertTrue(createdProfile.isParentKeywordDisabled(keyword));
   }

   private void testWidgetNotThere(SWTBot bot, final Type type, final String name) {
      boolean found = true;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         SWTBotPreferences.TIMEOUT = 500;
         switch (type) {
         case combo: {
            bot.comboBoxWithLabel(name);
            break;
         }
         case text: {
            bot.textWithLabel(name);
         }
         case table: {
            bot.tableWithLabel(name);
         }
         }
      }
      catch (final WidgetNotFoundException e) {
         found = false;
      }
      finally {
         SWTBotPreferences.TIMEOUT = originalTimeout;
      }
      assertFalse("Widget \"" + name + "\" should not be visible!", found);
   }

   private int getCheckedItemCount(final SWTBotTable table) {
      int count = 0;
      for (int i = 0; i < table.rowCount(); i++) {
         if (table.getTableItem(i).isChecked()) {
            count++;
         }
      }
      return count;
   }

   private String getCheckedItemFirstColumn(final SWTBotTable table) {
      for (int i = 0; i < table.rowCount(); i++) {
         final SWTBotTableItem item = table.getTableItem(i);
         if (item.isChecked()) {
            return item.getText(0);
         }
      }
      return null;
   }
}
