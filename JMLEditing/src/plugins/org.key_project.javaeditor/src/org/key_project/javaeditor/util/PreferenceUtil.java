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

package org.key_project.javaeditor.util;

import org.eclipse.jface.preference.IPreferenceStore;
import org.key_project.javaeditor.Activator;

/**
 * Provides utility methods to edit the preferences.
 * @author Martin Hentschel
 */
public final class PreferenceUtil {
   /**
    * Property to enable or disable the extensions.
    */
   public static final String PROP_EXTENSIONS_ENABLED = "org.key_project.javaeditor.extensionsEnabled";

   /**
    * Property to enable or disable a specific extensions extensions.
    */
   public static final String PROP_EXTENSION_ENABLED_PREFIX = "org.key_project.javaeditor.extensionEnabled_";

   /**
    * Forbid instances.
    */
   private PreferenceUtil() {
   }
   
   /**
    * Returns the {@link IPreferenceStore} to edit.
    * @return The used {@link IPreferenceStore}.
    */
   public static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Returns the current value of property {@link #PROP_EXTENSIONS_ENABLED}.
    * @return The current value of property{@link #PROP_EXTENSIONS_ENABLED}.
    */
   public static boolean isExtensionsEnabled() {
      return getStore().getBoolean(PROP_EXTENSIONS_ENABLED);
   }
   
   /**
    * Returns the default value of property {@link #PROP_EXTENSIONS_ENABLED}.
    * @return The default value of property{@link #PROP_EXTENSIONS_ENABLED}.
    */
   public static boolean isDefaultExtensionsEnabled() {
      return getStore().getDefaultBoolean(PROP_EXTENSIONS_ENABLED);
   }
   
   /**
    * Sets the current value of property {@link #PROP_EXTENSIONS_ENABLED}.
    * @param enabled The new value to set.
    */
   public static void setExtensionsEnabled(boolean enabled) {
      getStore().setValue(PROP_EXTENSIONS_ENABLED, enabled);
   }
   
   /**
    * Sets the default value of property {@link #PROP_EXTENSIONS_ENABLED}.
    * @param enabled The new value to set.
    */
   public static void setDefaultExtensionsEnabled(boolean enabled) {
      getStore().setDefault(PROP_EXTENSIONS_ENABLED, enabled);
   }
   
   /**
    * Returns the current value of property {@link #PROP_EXTENSIONS_ENABLED}.
    * @param id The ID of the extension.
    * @return The current value of property{@link #PROP_EXTENSIONS_ENABLED}.
    */
   public static boolean isExtensionEnabled(String id) {
      return getStore().getBoolean(PROP_EXTENSION_ENABLED_PREFIX + id);
   }
   
   /**
    * Returns the default value of property {@link #PROP_EXTENSIONS_ENABLED}.
    * @param id The ID of the extension.
    * @return The default value of property{@link #PROP_EXTENSIONS_ENABLED}.
    */
   public static boolean isDefaultExtensionEnabled(String id) {
      return getStore().getDefaultBoolean(PROP_EXTENSION_ENABLED_PREFIX + id);
   }
   
   /**
    * Sets the current value of property {@link #PROP_EXTENSIONS_ENABLED}.
    * @param id The ID of the extension.
    * @param enabled The new value to set.
    */
   public static void setExtensionEnabled(String id, boolean enabled) {
      getStore().setValue(PROP_EXTENSION_ENABLED_PREFIX + id, enabled);
   }
   
   /**
    * Sets the default value of property {@link #PROP_EXTENSIONS_ENABLED}.
    * @param id The ID of the extension.
    * @param enabled The new value to set.
    */
   public static void setDefaultExtensionEnabled(String id, boolean enabled) {
      getStore().setDefault(PROP_EXTENSION_ENABLED_PREFIX + id, enabled);
   }
}