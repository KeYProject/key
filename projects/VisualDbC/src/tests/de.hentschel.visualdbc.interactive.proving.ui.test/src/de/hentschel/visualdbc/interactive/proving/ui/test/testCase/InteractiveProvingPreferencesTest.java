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

package de.hentschel.visualdbc.interactive.proving.ui.test.testCase;

import junit.framework.TestCase;

import org.junit.Test;

import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveProvingPreferences;

/**
 * Tests for {@link InteractiveProvingPreferences}.
 * @author Martin Hentschel
 */
public class InteractiveProvingPreferencesTest extends TestCase {
   /**
    * Tests {@link InteractiveProvingPreferences#getPreferenceStore()}
    */
   @Test
   public void testGetPreferenceStore() {
      assertNotNull(InteractiveProvingPreferences.getPreferenceStore());
   }
   
   /**
    * Tests the property {@link InteractiveProvingPreferences#PROP_RESET_PROOF_IF_NEW_OPENED} via
    * {@link InteractiveProvingPreferences#isResetProofIfNewOpened()},
    * {@link InteractiveProvingPreferences#isDefaultResetProofIfNewOpened()},
    * {@link InteractiveProvingPreferences#setResetProofIfNewOpened(boolean)} and
    * {@link InteractiveProvingPreferences#setDefaultResetProofIfNewOpened(boolean)}.
    */
   @Test
   public void testResetProofIfNewOpened() {
      boolean defaultReset = InteractiveProvingPreferences.isDefaultResetProofIfNewOpened();
      boolean reset = InteractiveProvingPreferences.isResetProofIfNewOpened();
      try {
         // Test initial values
         assertEquals(true, InteractiveProvingPreferences.isResetProofIfNewOpened());
         assertEquals(true, InteractiveProvingPreferences.isDefaultResetProofIfNewOpened());
         // Set manual value
         InteractiveProvingPreferences.setResetProofIfNewOpened(false);
         assertEquals(false, InteractiveProvingPreferences.isResetProofIfNewOpened());
         assertEquals(true, InteractiveProvingPreferences.isDefaultResetProofIfNewOpened());
         // Set default value
         InteractiveProvingPreferences.setDefaultResetProofIfNewOpened(false);
         assertEquals(false, InteractiveProvingPreferences.isResetProofIfNewOpened());
         assertEquals(false, InteractiveProvingPreferences.isDefaultResetProofIfNewOpened());
         // Set manual value
         InteractiveProvingPreferences.setResetProofIfNewOpened(true);
         assertEquals(true, InteractiveProvingPreferences.isResetProofIfNewOpened());
         assertEquals(false, InteractiveProvingPreferences.isDefaultResetProofIfNewOpened());
         // Set default value
         InteractiveProvingPreferences.setDefaultResetProofIfNewOpened(true);
         assertEquals(true, InteractiveProvingPreferences.isResetProofIfNewOpened());
         assertEquals(true, InteractiveProvingPreferences.isDefaultResetProofIfNewOpened());
      }
      finally {
         InteractiveProvingPreferences.setDefaultResetProofIfNewOpened(defaultReset);
         InteractiveProvingPreferences.setResetProofIfNewOpened(reset);
      }
   }
}