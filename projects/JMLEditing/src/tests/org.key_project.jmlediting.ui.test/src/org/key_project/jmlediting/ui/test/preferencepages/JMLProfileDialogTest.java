package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertEquals;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTableItem;
import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.UITestUtils;

public class JMLProfileDialogTest {
   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private SWTBotTable profileTable;

   @BeforeClass
   public static void init() {
      UITestUtils.prepareWorkbench(bot);
   }

   @Before
   public void openGlobalProfileSettings() {
      UITestUtils.openGlobalSettings(bot);
      bot.sleep(100);
      this.navigateToJMLProfileSettings();
      this.setTable();
      bot.sleep(1000);
   }

   @After
   public void closeProfileSettings() {
      bot.button("OK").click();
   }

   private void setTable() {
      this.profileTable = bot.table();
   }

   private void navigateToJMLProfileSettings() {
      bot.tree().getTreeItem("JML").select().expand().getNode("Profile")
            .select();
   }

   @Test
   public void testCurrentProfileIsSelected() {
      final String selectedProfileName = this
            .getCheckedItemFirstColumn(this.profileTable);

      assertEquals("not the right Profile is selected", selectedProfileName,
            JMLPreferencesHelper.getDefaultJMLProfile().getName());
   }

   @Test
   public void testOnlyOneItemIsChecked() {
      final int count = this.getCheckedItemCount(this.profileTable);
      assertEquals("Less or more than 1 Profile is checked!", 1, count);
   }

   @Test
   public void testNewProfileSelection() {
      final SWTBotTableItem newProfileItem = this.profileTable.getTableItem(0);
      newProfileItem.check();
      bot.button("Apply").click();
      final String selectedProfileName = this
            .getCheckedItemFirstColumn(this.profileTable);
      assertEquals("The newly checked Profile gets not ",
            newProfileItem.getText(0), selectedProfileName);
   }

   @Test
   public void testViewProfile() {
      bot.button("View...").click();
      System.out.println(bot.textWithLabel("Profile Name:"));

      bot.sleep(100000);
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
