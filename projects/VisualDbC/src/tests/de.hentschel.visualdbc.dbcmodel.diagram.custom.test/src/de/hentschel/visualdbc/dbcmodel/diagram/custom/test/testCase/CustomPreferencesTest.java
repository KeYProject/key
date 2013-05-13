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

/**
 * Tests for {@link CustomPreferences}.
 * @author Martin Hentschel
 */
public class CustomPreferencesTest extends TestCase {
   /**
    * Tests {@link CustomPreferences#getPreferenceStore()}
    */
   @Test
   public void testGetPreferenceStore() {
      assertNotNull(CustomPreferences.getPreferenceStore());
   }
   
   /**
    * Tests the property {@link CustomPreferences#PROP_USE_CUSTOM_LAYOUT} via
    * {@link CustomPreferences#isUseCustomLayout()},
    * {@link CustomPreferences#isDefaultUseCustomLayout()},
    * {@link CustomPreferences#setUseCustomLayout(boolean)} and
    * {@link CustomPreferences#setDefaultUseCustomLayout(boolean)}.
    */
   @Test
   public void testUseCustomLayout() {
      boolean defaultUseCustomLayout = CustomPreferences.isDefaultUseCustomLayout();
      boolean useCustomLayout = CustomPreferences.isUseCustomLayout();
      try {
         // Test initial values
         assertEquals(true, CustomPreferences.isUseCustomLayout());
         assertEquals(true, CustomPreferences.isDefaultUseCustomLayout());
         // Set manual value
         CustomPreferences.setUseCustomLayout(false);
         assertEquals(false, CustomPreferences.isUseCustomLayout());
         assertEquals(true, CustomPreferences.isDefaultUseCustomLayout());
         // Set default value
         CustomPreferences.setDefaultUseCustomLayout(false);
         assertEquals(false, CustomPreferences.isUseCustomLayout());
         assertEquals(false, CustomPreferences.isDefaultUseCustomLayout());
         // Set manual value
         CustomPreferences.setUseCustomLayout(true);
         assertEquals(true, CustomPreferences.isUseCustomLayout());
         assertEquals(false, CustomPreferences.isDefaultUseCustomLayout());
         // Set default value
         CustomPreferences.setDefaultUseCustomLayout(true);
         assertEquals(true, CustomPreferences.isUseCustomLayout());
         assertEquals(true, CustomPreferences.isDefaultUseCustomLayout());
      }
      finally {
         CustomPreferences.setDefaultUseCustomLayout(defaultUseCustomLayout);
         CustomPreferences.setUseCustomLayout(useCustomLayout);
      }
   }
   
   /**
    * Tests the property {@link CustomPreferences#PROP_VERTICAL_SPACING} via
    * {@link CustomPreferences#getVerticalSpacing()},
    * {@link CustomPreferences#getDefaultVerticalSpacing()},
    * {@link CustomPreferences#setVerticalSpacing(int)} and
    * {@link CustomPreferences#setDefaultVerticalSpacing(int)}.
    */
   @Test
   public void testVerticalSpacing() {
      int defaultVerticalSpacing = CustomPreferences.getDefaultVerticalSpacing();
      int verticalSpacing = CustomPreferences.getVerticalSpacing();
      try {
         // Test initial values
         assertEquals(20, CustomPreferences.getVerticalSpacing());
         assertEquals(20, CustomPreferences.getDefaultVerticalSpacing());
         // Set manual value
         CustomPreferences.setVerticalSpacing(35);
         assertEquals(35, CustomPreferences.getVerticalSpacing());
         assertEquals(20, CustomPreferences.getDefaultVerticalSpacing());
         // Set default value
         CustomPreferences.setDefaultVerticalSpacing(35);
         assertEquals(35, CustomPreferences.getVerticalSpacing());
         assertEquals(35, CustomPreferences.getDefaultVerticalSpacing());
         // Set manual value
         CustomPreferences.setVerticalSpacing(20);
         assertEquals(20, CustomPreferences.getVerticalSpacing());
         assertEquals(35, CustomPreferences.getDefaultVerticalSpacing());
         // Set default value
         CustomPreferences.setDefaultVerticalSpacing(20);
         assertEquals(20, CustomPreferences.getVerticalSpacing());
         assertEquals(20, CustomPreferences.getDefaultVerticalSpacing());
      }
      finally {
         CustomPreferences.setDefaultVerticalSpacing(defaultVerticalSpacing);
         CustomPreferences.setVerticalSpacing(verticalSpacing);
      }
   }
}