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

package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import junit.framework.TestCase;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotRadio;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTabItem;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.preference.page.TacletOptionsPreferencePage;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.configuration.ChoiceSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * SWTBot tests for {@link TacletOptionsPreferencePage}.
 * @author Martin Hentschel
 */
public class SWTBotTacletOptionsPreferencePageTest extends TestCase {
   /**
    * Tests the shown categories and values and finally approves the made changes.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testApprove() throws Exception {
      doTestShownValuesAndModification(true);
   }

   /**
    * Tests the shown categories and values and finally cancels the made changes.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testCancel() throws Exception {
      doTestShownValuesAndModification(false);
   }

   /**
    * Executes the test steps of {@link #testApprove()} and {@link #testCancel()}.
    * @param approve {@code true} approve, {@code false} cancel. 
    * @throws Exception Occurred Exception.
    */
   protected void doTestShownValuesAndModification(boolean approve) throws Exception{
      // Make sure that runtime options are available
      if (!SymbolicExecutionUtil.isChoiceSettingInitialised()) {
         TacletOptionsPreferencePage.loadChoiceSettings();
      }
      assertTrue(SymbolicExecutionUtil.isChoiceSettingInitialised());
      // Get original settings
      ChoiceSettings oldSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
      assertNotNull(oldSettings);
      HashMap<String, String> oldDefaultChoices = oldSettings.getDefaultChoices();
      assertNotNull(oldDefaultChoices);
      assertTrue(!oldDefaultChoices.isEmpty());
      Map<String, Set<String>> oldChoices = oldSettings.getChoices();
      assertNotNull(oldChoices);
      assertTrue(!oldChoices.isEmpty());
      SWTBotShell preferenceShell = null;
      try {
         // Create bot
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         preferenceShell = TestUtilsUtil.openPreferencePage(bot, "KeY", "Taclet Options");
         // Test shown categories, values and selected values
         Map<String, String> expectedNewValues = new HashMap<String, String>();
         Set<Entry<String, Set<String>>> entries = oldChoices.entrySet();
         assertFalse(entries.isEmpty());
         for (Entry<String, Set<String>> entry : entries) {
            String category = entry.getKey();
            SWTBotTabItem tabItem = preferenceShell.bot().tabItem(category);
            tabItem.activate();
            assertTrue(entries.size() >= 2);
            for (String value : entry.getValue()) {
               SWTBotRadio radio = preferenceShell.bot().radio(value);
               boolean oldSelected = ObjectUtil.equals(oldDefaultChoices.get(category), radio.getText());
               assertEquals(oldSelected, radio.isSelected());
            }
         }
         // Change value in each category
         for (Entry<String, Set<String>> entry : entries) {
            String category = entry.getKey();
            SWTBotTabItem tabItem = preferenceShell.bot().tabItem(category);
            tabItem.activate();
            for (String value : entry.getValue()) {
               SWTBotRadio radio = preferenceShell.bot().radio(value);
               boolean oldSelected = ObjectUtil.equals(oldDefaultChoices.get(category), radio.getText());
               // Select radio if not selected before
               if (!oldSelected) {
                  radio.click();
                  expectedNewValues.put(category, radio.getText());
               }
            }
         }
         // Close dialog
         if (approve) {
            preferenceShell.bot().button("OK").click();
         }
         else {
            preferenceShell.bot().button("Cancel").click();
         }
         // Test current values
         ChoiceSettings newSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
         assertNotNull(oldSettings);
         Map<String, String> newDefaultChoices = newSettings.getDefaultChoices();
         assertNotNull(oldDefaultChoices);
         assertTrue(!oldDefaultChoices.isEmpty());
         Set<Entry<String, String>> newDefaultChoiceEntries = newDefaultChoices.entrySet();
         for (Entry<String, String> entry : newDefaultChoiceEntries) {
            if (approve) {
               assertEquals(expectedNewValues.get(entry.getKey()), entry.getValue());
            }
            else {
               assertEquals(oldDefaultChoices.get(entry.getKey()), entry.getValue());
            }
         }
      }
      finally {
         // Restore preferences
         oldSettings.setDefaultChoices(oldDefaultChoices);
         // Close preference dialog
         if (preferenceShell != null && preferenceShell.isOpen()) {
            preferenceShell.close();
         }
      }
   }
}