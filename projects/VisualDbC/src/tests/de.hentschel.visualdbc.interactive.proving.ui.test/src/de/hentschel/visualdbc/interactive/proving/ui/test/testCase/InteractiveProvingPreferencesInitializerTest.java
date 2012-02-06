/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.interactive.proving.ui.test.testCase;

import junit.framework.TestCase;

import org.junit.Test;

import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveProvingPreferences;
import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveProvingPreferencesInitializer;

/**
 * Tests for {@link InteractiveProvingPreferencesInitializer}.
 * @author Martin Hentschel
 */
public class InteractiveProvingPreferencesInitializerTest extends TestCase {
   /**
    * Tests the defined default values in {@link InteractiveProvingPreferencesInitializer#initializeDefaultPreferences()}.
    */
   @Test
   public void testDefaultValues() {
      assertEquals(true, InteractiveProvingPreferences.isDefaultResetProofIfNewOpened());
   }
}
