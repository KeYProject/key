package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTableItem;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.ui.test.UITestUtils;

public class JMLKeywordDialogTest {
   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static final String PROFILE_NAME = "Profile Name:";
   private static final String DERIVED_FROM = "Derived from:";
   private static final String NEW_PROFILE_NAME = "TestProfile123";
   private static final String PROFILENAME_TO_SELECT = "KeY Profile";
   private static final String PROFILETABLE_LABEL = "Choose active JML Profile from available ones:";

   private static final String KEYWORD_LABEL = "Keyword:";
   private static final String CUSTOM_KEYWORD_TABLE = "Custom Keywords:";

   private static final String NEW_KEYWORD = "\\test";
   private static final String SECOND_KEYWORD = "highvalue";

   @BeforeClass
   public static void init() {
      UITestUtils.prepareWorkbench(bot);
      bot.sleep(100);
      UITestUtils.openGlobalSettings(bot);
      bot.sleep(100);
      navigateToJMLProfileSettings();
      createNewProfileAndOpen();
   }

   private static void createNewProfileAndOpen() {
      bot.button("New...").click();
      bot.textWithLabel(PROFILE_NAME).setText(NEW_PROFILE_NAME);
      bot.comboBoxWithLabel(DERIVED_FROM).setSelection(PROFILENAME_TO_SELECT);
      bot.sleep(100);
      clickOK();
      bot.tableWithLabel(PROFILETABLE_LABEL).getTableItem(NEW_PROFILE_NAME)
            .select();
      bot.button("Edit...").click();
   }

   @Test
   public void testKeywordDialog() {
      bot.button("New...").click();
      SWTBotText keywordText = bot.textWithLabel(KEYWORD_LABEL);
      keywordText.setText(NEW_KEYWORD);
      clickOK();

      SWTBotTable customKeywordsTable = bot
            .tableWithLabel(CUSTOM_KEYWORD_TABLE);
      assertEquals("New Keyword is not Saved!", 1,
            customKeywordsTable.rowCount());
      assertEquals("New Keyword has wrong Name!", NEW_KEYWORD,
            this.getFirstItemFirstColumn(customKeywordsTable));
      assertTrue("Keyword not saved in ProfileManagement",
            this.profileContainsKeyword(NEW_PROFILE_NAME, NEW_KEYWORD));
      assertFalse("Wrong Keyword saved in ProfileManagement",
            this.profileContainsKeyword(NEW_PROFILE_NAME, SECOND_KEYWORD));

      customKeywordsTable.getTableItem(0).select();
      bot.button("Edit...").click();
      keywordText = bot.textWithLabel(KEYWORD_LABEL);
      keywordText.setText(SECOND_KEYWORD);
      clickOK();
      bot.sleep(100);
      assertEquals("New Keyword is not Saved!", 1,
            customKeywordsTable.rowCount());
      assertEquals("New Keyword has wrong Name!", SECOND_KEYWORD,
            this.getFirstItemFirstColumn(customKeywordsTable));

      assertTrue("Keyword not saved in ProfileManagement",
            this.profileContainsKeyword(NEW_PROFILE_NAME, SECOND_KEYWORD));
      assertFalse("Keyword not saved in ProfileManagement",
            this.profileContainsKeyword(NEW_PROFILE_NAME, NEW_KEYWORD));

      customKeywordsTable = bot.tableWithLabel(CUSTOM_KEYWORD_TABLE);
      customKeywordsTable.getTableItem(0).select();
      bot.button("Remove...").click();
      clickOK();
      assertFalse("Keyword not removed!",
            this.profileContainsKeyword(NEW_PROFILE_NAME, NEW_KEYWORD));
      assertFalse("Keyword not removed!",
            this.profileContainsKeyword(NEW_PROFILE_NAME, SECOND_KEYWORD));
      assertEquals("Keyword not removed!", 0, customKeywordsTable.rowCount());

   }

   private boolean profileContainsKeyword(final String profileName,
         final String keywordString) {
      final IJMLProfile profile = JMLProfileManagement.instance()
            .getProfileFromName(profileName);
      for (final IKeyword keyword : profile.getSupportedKeywords()) {
         if (keyword.getKeywords().contains(keywordString)) {
            return true;
         }
      }
      return false;
   }

   private static void navigateToJMLProfileSettings() {
      bot.tree().getTreeItem("JML").select().expand().getNode("Profile")
            .select();
   }

   private static void clickOK() {
      bot.button("OK").click();
   }

   private String getFirstItemFirstColumn(final SWTBotTable table) {
      final SWTBotTableItem item = table.getTableItem(0);
      return item.getText(0);
   }
}
