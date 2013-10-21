/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.dbcmodel.diagram.custom.test.testCase.swtbot;

import junit.framework.TestCase;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.Test;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.dbcmodel.diagram.custom.util.CustomPreferences;

/**
 * SWT Bot tests for DbCModelLayoutPreferencePage. 
 * @author Martin Hentschel
 */
public class SWTBotDbCModelLayoutPreferencePageTest extends TestCase {
   /**
    * Tests shown values and set new values.
    */
   @Test
   public void testSettingValues() {
      boolean useCustomLayout = CustomPreferences.isUseCustomLayout();
      int verticalSpacing = CustomPreferences.getVerticalSpacing();
      try {
         // Create bot
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         // Close welcome perspective
         TestUtilsUtil.closeWelcomeView(bot);
         // Open preference page and change values
         SWTBotShell shell = TestUtilsUtil.openPreferencePage(bot, "DbC Diagram", "Layout");
         compareAndSetValue(shell, CustomPreferences.isUseCustomLayout(), CustomPreferences.getVerticalSpacing(), false, 12, true);
         // Open preference page and change values again
         shell = TestUtilsUtil.openPreferencePage(bot, "DbC Diagram", "Layout");
         compareAndSetValue(shell, CustomPreferences.isUseCustomLayout(), CustomPreferences.getVerticalSpacing(), true, 13, true);
         // Open preference page and change values again
         shell = TestUtilsUtil.openPreferencePage(bot, "DbC Diagram", "Layout");
         compareAndSetValue(shell, CustomPreferences.isUseCustomLayout(), CustomPreferences.getVerticalSpacing(), false, 14, true);
         // Open preference page and change values again and cancel it
         shell = TestUtilsUtil.openPreferencePage(bot, "DbC Diagram", "Layout");
         compareAndSetValue(shell, CustomPreferences.isUseCustomLayout(), CustomPreferences.getVerticalSpacing(), true, 15, false);
         // Open preference page and restore default values
         shell = TestUtilsUtil.openPreferencePage(bot, "DbC Diagram", "Layout");
         shell.bot().button("Restore Defaults").click();
         compareAndSetValue(shell, CustomPreferences.isDefaultUseCustomLayout(), CustomPreferences.getDefaultVerticalSpacing(), null, null, true);
      }
      finally {
         CustomPreferences.setUseCustomLayout(useCustomLayout);
         CustomPreferences.setVerticalSpacing(verticalSpacing);
      }
   }
   
   /**
    * Compares the shown values in the preference page and defines new values.
    * @param shell The {@link SWTBotShell} to use.
    * @param shownCustomLayout The initial use custom layout value.
    * @param shownVerticalSpacing The initial vertical spacing value.
    * @param customLayoutToSet The custom layout value to set or {@code null} if no change required.
    * @param verticalSpacingToSet The vertical spacing to set or {@code null} if no change required.
    * @param commit {@code true} = commit dialog, {@code false} = cancel dialog.
    */
   protected void compareAndSetValue(SWTBotShell shell,
                                     boolean shownCustomLayout,
                                     int shownVerticalSpacing,
                                     Boolean customLayoutToSet,
                                     Integer verticalSpacingToSet,
                                     boolean commit) {
      // Check shown values
      SWTBotCheckBox useLayoutBox = shell.bot().checkBox("Use custom layout");
      SWTBotText verticalText = shell.bot().textWithLabel("Vertical spacing");
      assertEquals(shownCustomLayout, useLayoutBox.isChecked());
      assertEquals(shownVerticalSpacing + "", verticalText.getText());
      // Change values
      if (customLayoutToSet != null) {
         if (Boolean.TRUE.equals(customLayoutToSet)) {
            useLayoutBox.select();
         }
         else {
            useLayoutBox.deselect();
         }
      }
      if (verticalSpacingToSet != null) {
         verticalText.setText(verticalSpacingToSet.toString());
      }
      // Close dialog
      if (commit) {
         shell.bot().button("OK").click();
      }
      else {
         shell.bot().button("Cancel").click();
      }
      // Compare defined preferences
      if (commit && customLayoutToSet != null) {
         assertEquals(customLayoutToSet.booleanValue(), CustomPreferences.isUseCustomLayout());
      }
      else {
         assertEquals(shownCustomLayout, CustomPreferences.isUseCustomLayout());
      }
      if (commit && verticalSpacingToSet != null) {
         assertEquals(verticalSpacingToSet.intValue(), CustomPreferences.getVerticalSpacing());
      }
      else {
         assertEquals(shownVerticalSpacing, CustomPreferences.getVerticalSpacing());
      }
   }
}