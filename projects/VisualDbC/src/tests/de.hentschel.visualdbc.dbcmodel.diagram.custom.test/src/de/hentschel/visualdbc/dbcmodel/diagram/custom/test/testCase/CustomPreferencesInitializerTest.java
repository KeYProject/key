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

package de.hentschel.visualdbc.dbcmodel.diagram.custom.test.testCase;

import junit.framework.TestCase;

import org.junit.Test;

import de.hentschel.visualdbc.dbcmodel.diagram.custom.util.CustomPreferences;
import de.hentschel.visualdbc.dbcmodel.diagram.custom.util.CustomPreferencesInitializer;

/**
 * Tests for {@link CustomPreferencesInitializer}.
 * @author Martin Hentschel
 */
public class CustomPreferencesInitializerTest extends TestCase {
   /**
    * Tests the defined default values in {@link CustomPreferencesInitializer#initializeDefaultPreferences()}.
    */
   @Test
   public void testDefaultValues() {
      assertEquals(true, CustomPreferences.isDefaultUseCustomLayout());
      assertEquals(20, CustomPreferences.getDefaultVerticalSpacing());
   }
}