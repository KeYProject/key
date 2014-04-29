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

package de.hentschel.visualdbc.dbcmodel.diagram.custom.util;

import org.eclipse.jface.preference.IPreferenceStore;

import de.hentschel.visualdbc.dbcmodel.diagram.custom.Activator;
import de.hentschel.visualdbc.dbcmodel.diagram.custom.preference.DbCModelLayoutPreferencePage;

/**
 * <p>
 * Provides static methods and constant to access the custom layout preferences.
 * </p>
 * <p>
 * The initial values are defined via {@link CustomPreferencesInitializer}.
 * </p>
 * <p>
 * The user can modify the values via the preference pages
 * {@link DbCModelLayoutPreferencePage}.
 * </p>
 * @author Martin Hentschel
 * @see CustomPreferencesInitializer
 * @see DbCModelLayoutPreferencePage
 */
public final class CustomPreferences {
   /**
    * The property: use custom layout
    */
   public static final String PROP_USE_CUSTOM_LAYOUT = "de.hentschel.visualdbc.dbcmodel.diagram.custom.layout.useCustomlayout";

   /**
    * The property: vertical spacing
    */
   public static final String PROP_VERTICAL_SPACING = "de.hentschel.visualdbc.dbcmodel.diagram.custom.layout.verticalSpacing";
   
   /**
    * Forbid instances.
    */
   private CustomPreferences() {
   }

   /**
    * Returns the used {@link IPreferenceStore}.
    * @return The {@link IPreferenceStore} to use.
    */
   public static IPreferenceStore getPreferenceStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Checks if the custom layout should be used or not.
    * @return {@code true} = use custom layout, {@code false} = don't use custom layout.
    */
   public static boolean isUseCustomLayout() {
      return getPreferenceStore().getBoolean(PROP_USE_CUSTOM_LAYOUT);
   }
   
   /**
    * Checks if the custom layout should be used or not by default.
    * @return {@code true} = use custom layout, {@code false} = don't use custom layout.
    */
   public static boolean isDefaultUseCustomLayout() {
      return getPreferenceStore().getDefaultBoolean(PROP_USE_CUSTOM_LAYOUT);
   }
   
   /**
    * Sets the use custom layout value.
    * @param useCustomLayout The value to set.
    */
   public static void setUseCustomLayout(boolean useCustomLayout) {
      getPreferenceStore().setValue(PROP_USE_CUSTOM_LAYOUT, useCustomLayout);
   }
   
   /**
    * Sets the default use custom layout value.
    * @param defaultUseCustomLayout The default value to set.
    */
   public static void setDefaultUseCustomLayout(boolean defaultUseCustomLayout) {
      getPreferenceStore().setDefault(PROP_USE_CUSTOM_LAYOUT, defaultUseCustomLayout);
   }
   
   /**
    * Returns the vertical spacing to use.
    * @return The used vertical spacing.
    */
   public static int getVerticalSpacing() {
      return getPreferenceStore().getInt(PROP_VERTICAL_SPACING);
   }
   
   /**
    * Returns the default vertical spacing.
    * @return The used vertical spacing.
    */
   public static int getDefaultVerticalSpacing() {
      return getPreferenceStore().getDefaultInt(PROP_VERTICAL_SPACING);
   }
   
   /**
    * Sets the vertical spacing.
    * @param verticalSpacing The vertical spacing to use.
    */
   public static void setVerticalSpacing(int verticalSpacing) {
      getPreferenceStore().setValue(PROP_VERTICAL_SPACING, verticalSpacing);
   }
   
   /**
    * Sets the default vertical spacing.
    * @param defaultVerticalSpacing The default value to set.
    */
   public static void setDefaultVerticalSpacing(int defaultVerticalSpacing) {
      getPreferenceStore().setDefault(PROP_VERTICAL_SPACING, defaultVerticalSpacing);
   }
}