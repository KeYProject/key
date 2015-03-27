package org.key_project.jmlediting.ui.test.preferencepages;

import static org.eclipse.swtbot.swt.finder.SWTBotAssert.assertNotEnabled;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTableItem;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.ui.test.UITestUtils;

public class JMLProfileDialogTest {
   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static final String PROFILE_NAME = "Profile Name:";
   private static final String DERIVED_FROM = "Derived from:";
   private static final String KEYWORDTABLE_VIEW = "Supported Keywords";
   private static final String KEYWORDTABLE_EDIT = "Keywords from parent profile:";
   private static final String DERIVEDTABLE = "Custom Keywords:";
   private static final String PROFILETABLE_LABEL = "Choose active JML Profile from available ones:";

   private static final String NEW_PROFILE_NAME = "TestProfile123";
   private static final String SECOND_NEW_PROFILE_NAME = "SecondProfile";
   private static final String PROFILENAME_TO_SELECT = "KeY Profile";

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
      UITestUtils.prepareWorkbench(bot);
   }

   @Before
   public void openGlobalProfileSettings() {
      UITestUtils.openGlobalSettings(bot);
      bot.sleep(100);
      this.navigateToJMLProfileSettings();
      bot.sleep(1000);
   }

   @After
   public void closeProfileSettings() {
      bot.button("Cancel").click();
      try {
         bot.button("Cancel").click();
         bot.button("Cancel").click();
         bot.button("Cancel").click();
      }
      catch (final Exception e) {
         // close all dialogs, not clear how much, max 4.
      }
   }

   private void navigateToJMLProfileSettings() {
      bot.tree().getTreeItem("JML").select().expand().getNode("Profile")
            .select();
   }

   @Test
   public void testCurrentProfileIsSelected() {
      final String selectedProfileName = this.getCheckedItemFirstColumn(bot
            .tableWithLabel(PROFILETABLE_LABEL));

      assertEquals("not the right Profile is selected", selectedProfileName,
            JMLPreferencesHelper.getDefaultJMLProfile().getName());
   }

   @Test
   public void testOnlyOneItemIsChecked() {
      final int count = this.getCheckedItemCount(bot
            .tableWithLabel(PROFILETABLE_LABEL));
      assertEquals("Less or more than 1 Profile is checked!", 1, count);
   }

   @Test
   public void testNewProfileSelection() {
      final String currentProfileName = this.getCheckedItemFirstColumn(bot
            .tableWithLabel(PROFILETABLE_LABEL));
      final SWTBotTableItem newProfileItem = bot.tableWithLabel(
            PROFILETABLE_LABEL).getTableItem(PROFILENAME_TO_SELECT);
      newProfileItem.check();
      bot.button("Apply").click();
      bot.sleep(100);
      bot.button("Yes").click();
      bot.sleep(500);
      final String selectedProfileName = this.getCheckedItemFirstColumn(bot
            .tableWithLabel(PROFILETABLE_LABEL));
      assertEquals("The newly checked Profile gets not ",
            newProfileItem.getText(0), selectedProfileName);
      bot.tableWithLabel(PROFILETABLE_LABEL).getTableItem(currentProfileName)
            .check();
      bot.button("Apply").click();
   }

   @Test
   public void testViewProfile() {
      final IJMLProfile profile = JMLPreferencesHelper.getDefaultJMLProfile();
      bot.button("View...").click();
      final SWTBotText profileNameText = bot.textWithLabel(PROFILE_NAME);
      assertNotEnabled(profileNameText);
      assertEquals("Profile Name is not set correct!", profile.getName(),
            profileNameText.getText());

      final SWTBotTable table = bot.tableWithLabel(KEYWORDTABLE_VIEW);
      assertEquals("Not the right amount of keywords is shown", profile
            .getSupportedKeywords().size(), table.rowCount());

      this.testWidgetNotThere(Type.combo, DERIVED_FROM);
      this.testWidgetNotThere(Type.table, DERIVEDTABLE);
   }

   /**
    * need this in order, because only a derived profile can be edited, and by
    * default there is no derived profile...
    */
   @Test
   public void testNewAndEditProfile() {
      this.testNewProfileAndSave();
      this.testEditProfile();
   }

   private void testEditProfile() {
      bot.tableWithLabel(PROFILETABLE_LABEL).getTableItem(NEW_PROFILE_NAME)
            .select();
      bot.button("Edit...").click();

      assertFalse("DerivedFromCombo should be disabled!", bot
            .comboBoxWithLabel(DERIVED_FROM).isEnabled());

      final SWTBotTable keywordTable = bot.tableWithLabel(KEYWORDTABLE_EDIT);

      assertFalse("Disabled Keyword is not saved!", keywordTable
            .getTableItem(0).isChecked());
      boolean allOtherChecked = true;
      for (int i = 1; i < keywordTable.rowCount(); i++) {
         if (allOtherChecked) {
            allOtherChecked = keywordTable.getTableItem(2).isChecked();
         }
      }
      assertTrue("Too many Keywords are disabled!", allOtherChecked);

      final SWTBotText profileNameText = bot.textWithLabel(PROFILE_NAME);
      profileNameText.setText(SECOND_NEW_PROFILE_NAME);

      this.clickOK();

      assertTrue(
            "Edit Profile was not successfull! (edit name not saved)",
            bot.tableWithLabel(PROFILETABLE_LABEL).containsItem(
                  SECOND_NEW_PROFILE_NAME)
                  && !bot.tableWithLabel(PROFILETABLE_LABEL).containsItem(
                        NEW_PROFILE_NAME));
   }

   private void testNewProfileAndSave() {
      bot.button("New...").click();

      // first check validation
      this.clickOK();
      bot.textWithLabel(PROFILE_NAME).setText(NEW_PROFILE_NAME);
      this.clickOK();
      // no recycling of variables, so we can test, that the dialog is not
      // closed.
      bot.textWithLabel(PROFILE_NAME).setText("");
      bot.comboBoxWithLabel(DERIVED_FROM).setSelection(PROFILENAME_TO_SELECT);
      this.clickOK();
      bot.textWithLabel(PROFILE_NAME).setText(NEW_PROFILE_NAME);

      final IJMLProfile selectedProfile = JMLProfileManagement.instance()
            .getProfileFromName(PROFILENAME_TO_SELECT);
      final SWTBotTable keywordTable = bot.tableWithLabel(KEYWORDTABLE_EDIT);
      assertEquals("Not the right amount of keywords is shown!",
            selectedProfile.getSupportedKeywords().size(),
            keywordTable.rowCount());

      keywordTable.getTableItem(0).uncheck();
      this.clickOK();

      assertTrue(
            "New Profile is not saved!",
            bot.tableWithLabel(PROFILETABLE_LABEL).containsItem(
                  NEW_PROFILE_NAME));
   }

   private void testWidgetNotThere(final Type type, final String name) {
      boolean found = true;
      try {
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

   private void clickOK() {
      bot.button("OK").click();
   }
}
