package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTableItem;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotJMLKeywordWizardTest {
   private static final String PROFILE_NAME = "Profile Name:";
   private static final String DERIVED_FROM = "Derived from:";
   private static final String NEW_PROFILE_NAME = "KeywordTestProfile";
   private static final String PROFILENAME_TO_SELECT = "KeY Profile";
   private static final String PROFILETABLE_LABEL = "Choose active JML Profile from available ones:";

   private static final String KEYWORD_LABEL = "Keyword:";
   private static final String CUSTOM_KEYWORD_TABLE = "Custom Keywords:";

   private static final String NEW_KEYWORD = "\\test";
   private static final String SECOND_KEYWORD = "highvalue";

   @BeforeClass
   public static void init() {
      TestUtilsUtil.closeWelcomeView();
   }

   @Test
   public void testKeywordDialog() {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotShell preferenceShell = JMLEditingUITestUtils.openJMLProfilePreferencePage(bot);
      SWTBotShell editShell = createNewProfileAndOpen(preferenceShell, true);
      editShell.bot().button("New...").click();
      
      SWTBotShell newKeywordShell = editShell.bot().shell("Create New Keyword");
      SWTBotText keywordText = newKeywordShell.bot().textWithLabel(KEYWORD_LABEL);
      keywordText.setText(NEW_KEYWORD);
      clickOK(newKeywordShell);

      SWTBotTable customKeywordsTable = editShell.bot().tableWithLabel(CUSTOM_KEYWORD_TABLE);
      assertEquals("New Keyword is not Saved!", 1, customKeywordsTable.rowCount());
      assertEquals("New Keyword has wrong Name!", NEW_KEYWORD, this.getFirstItemFirstColumn(customKeywordsTable));
      assertFalse("Keyword saved in ProfileManagement", this.profileContainsKeyword(NEW_PROFILE_NAME, NEW_KEYWORD));
      assertFalse("Wrong Keyword saved in ProfileManagement", this.profileContainsKeyword(NEW_PROFILE_NAME, SECOND_KEYWORD));

      customKeywordsTable.getTableItem(0).select();
      editShell.bot().button("Edit...").click();
      
      SWTBotShell editKeywordShell = editShell.bot().shell("Edit Keyword");
      keywordText = editKeywordShell.bot().textWithLabel(KEYWORD_LABEL);
      keywordText.setText(SECOND_KEYWORD);
      clickOK(editKeywordShell);
      
      assertEquals("New Keyword is not Saved!", 1, customKeywordsTable.rowCount());
      assertEquals("New Keyword has wrong Name!", SECOND_KEYWORD, this.getFirstItemFirstColumn(customKeywordsTable));

      assertFalse("Keyword saved in ProfileManagement", this.profileContainsKeyword(NEW_PROFILE_NAME, SECOND_KEYWORD));
      assertFalse("Keyword saved in ProfileManagement", this.profileContainsKeyword(NEW_PROFILE_NAME, NEW_KEYWORD));

      clickOK(editShell);
      assertTrue("Keyword not saved in ProfileManagement", this.profileContainsKeyword(NEW_PROFILE_NAME, SECOND_KEYWORD));
      assertFalse("Keyword saved in ProfileManagement", this.profileContainsKeyword(NEW_PROFILE_NAME, NEW_KEYWORD));
      
      editShell = createNewProfileAndOpen(preferenceShell, false);
      customKeywordsTable = editShell.bot().tableWithLabel(CUSTOM_KEYWORD_TABLE);
      
      customKeywordsTable.getTableItem(0).select();
      editShell.bot().button("Remove...").click();
      SWTBotShell confirmShell = editShell.bot().shell("Remove Keyword");
      clickOK(confirmShell);
      assertEquals("Keyword not removed!", 0, customKeywordsTable.rowCount());
      assertTrue("Keyword not saved in ProfileManagement", this.profileContainsKeyword(NEW_PROFILE_NAME, SECOND_KEYWORD));
      assertFalse("Keyword saved in ProfileManagement", this.profileContainsKeyword(NEW_PROFILE_NAME, NEW_KEYWORD));

      clickOK(editShell);
      assertFalse("Keyword not removed!", this.profileContainsKeyword(NEW_PROFILE_NAME, NEW_KEYWORD));
      assertFalse("Keyword not removed!", this.profileContainsKeyword(NEW_PROFILE_NAME, SECOND_KEYWORD));
      clickOK(preferenceShell);
   }

   private static SWTBotShell createNewProfileAndOpen(SWTBotShell preferenceShell, boolean createProfile) {
      if (createProfile) {
         preferenceShell.bot().button("New...").click();
         SWTBotShell newShell = preferenceShell.bot().shell("Create Profile");
         newShell.bot().textWithLabel(PROFILE_NAME).setText(NEW_PROFILE_NAME);
         newShell.bot().comboBoxWithLabel(DERIVED_FROM).setSelection(PROFILENAME_TO_SELECT);
         clickOK(newShell);
      }
      
      preferenceShell.bot().tableWithLabel(PROFILETABLE_LABEL).getTableItem(NEW_PROFILE_NAME).select();
      preferenceShell.bot().button("Edit...").click();
      return preferenceShell.bot().shell("Edit Profile");
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

   private static void clickOK(SWTBotShell shell) {
      shell.bot().button(IDialogConstants.OK_LABEL).click();
      shell.bot().waitUntil(Conditions.shellCloses(shell));
   }

   private String getFirstItemFirstColumn(final SWTBotTable table) {
      final SWTBotTableItem item = table.getTableItem(0);
      return item.getText(0);
   }
}
