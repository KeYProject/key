// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.util;

import java.util.HashMap;

import junit.framework.TestCase;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

/**
 * Tests for {@link SymbolicExecutionUtil}
 * @author Martin Hentschel
 */
public class TestSymbolicExecutionUtil extends TestCase {
   /**
    * Tests {@link SymbolicExecutionUtil#getChoiceSetting(String)} and
    * {@link SymbolicExecutionUtil#setChoiceSetting(String, String)} and
    * {@link SymbolicExecutionUtil#isChoiceSettingInitialised()}.
    */
   public void testGetAndSetChoiceSetting() throws Exception {
      String originalValue = null; 
      try {
         assertTrue(SymbolicExecutionUtil.isChoiceSettingInitialised());
         // Store default choice settings
         HashMap<String, String> defaultSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
         assertFalse(defaultSettings.isEmpty());
         // Test initial value
         originalValue = SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);
         assertTrue(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW.equals(originalValue) || SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_BAN.equals(originalValue));
         // Change value and make sure that it has changed
         String newValue = SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW.equals(originalValue) ? SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_BAN : SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW; 
         SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, newValue);
         assertEquals(newValue, SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS));
         // Make sure that all other settings are unchanged.
         HashMap<String, String> changedSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
         defaultSettings.put(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, newValue);
         assertEquals(defaultSettings, changedSettings);
      }
      finally {
         if (originalValue != null) {
            SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalValue);
         }
      }
   }
}