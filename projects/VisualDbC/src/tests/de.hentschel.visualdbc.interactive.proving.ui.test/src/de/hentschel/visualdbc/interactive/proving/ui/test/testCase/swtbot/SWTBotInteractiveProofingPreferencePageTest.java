/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

package de.hentschel.visualdbc.interactive.proving.ui.test.testCase.swtbot;

import junit.framework.TestCase;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.Test;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveProvingPreferences;

/**
 * SWT Bot tests for InteractiveProofingPreferencePage. 
 * @author Martin Hentschel
 */
public class SWTBotInteractiveProofingPreferencePageTest extends TestCase {
   /**
    * Tests shown values and set new values.
    */
   @Test
   public void testSettingValues() {
      boolean resetProof = InteractiveProvingPreferences.isResetProofIfNewOpened();
      try {
         // Create bot
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         // Close welcome perspective
         TestUtilsUtil.closeWelcomeView(bot);
         // Open preference page and change values
         SWTBotShell shell = TestUtilsUtil.openPreferencePage(bot, "DbC Diagram", "Interactive proofing");
         compareAndSetValue(shell, InteractiveProvingPreferences.isResetProofIfNewOpened(), false, true);
         // Open preference page and change values again
         shell = TestUtilsUtil.openPreferencePage(bot, "DbC Diagram", "Interactive proofing");
         compareAndSetValue(shell, InteractiveProvingPreferences.isResetProofIfNewOpened(), true, true);
         // Open preference page and change values again
         shell = TestUtilsUtil.openPreferencePage(bot, "DbC Diagram", "Interactive proofing");
         compareAndSetValue(shell, InteractiveProvingPreferences.isResetProofIfNewOpened(), false, true);
         // Open preference page and change values again and cancel it
         shell = TestUtilsUtil.openPreferencePage(bot, "DbC Diagram", "Interactive proofing");
         compareAndSetValue(shell, InteractiveProvingPreferences.isResetProofIfNewOpened(), true, false);
         // Open preference page and restore default values
         shell = TestUtilsUtil.openPreferencePage(bot, "DbC Diagram", "Interactive proofing");
         shell.bot().button("Restore Defaults").click();
         compareAndSetValue(shell, InteractiveProvingPreferences.isDefaultResetProofIfNewOpened(), null, true);
      }
      finally {
         InteractiveProvingPreferences.setResetProofIfNewOpened(resetProof);
      }
   }
   
   /**
    * Compares the shown values in the preference page and defines new values.
    * @param shell The {@link SWTBotShell} to use.
    * @param shownResetProof The initial use custom layout value.
    * @param resetProofToSet The custom layout value to set or {@code null} if no change required.
    * @param commit {@code true} = commit dialog, {@code false} = cancel dialog.
    */
   protected void compareAndSetValue(SWTBotShell shell,
                                     boolean shownResetProof,
                                     Boolean resetProofToSet,
                                     boolean commit) {
      // Check shown values
      SWTBotCheckBox useLayoutBox = shell.bot().checkBox("Reset model proofs when new interactive proof starts");
      assertEquals(shownResetProof, useLayoutBox.isChecked());
      // Change values
      if (resetProofToSet != null) {
         if (Boolean.TRUE.equals(resetProofToSet)) {
            useLayoutBox.select();
         }
         else {
            useLayoutBox.deselect();
         }
      }
      // Close dialog
      if (commit) {
         shell.bot().button("OK").click();
      }
      else {
         shell.bot().button("Cancel").click();
      }
      // Compare defined preferences
      if (commit && resetProofToSet != null) {
         assertEquals(resetProofToSet.booleanValue(), InteractiveProvingPreferences.isResetProofIfNewOpened());
      }
      else {
         assertEquals(shownResetProof, InteractiveProvingPreferences.isResetProofIfNewOpened());
      }
   }
}