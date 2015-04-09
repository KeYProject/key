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

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
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
    * The extension point providing {@link IPreferenceListener}.
    */
   public static final String LISTENER_EXTENSION_POINT = "org.key_project.javaeditor.javaEditorPreferenceListener";
   
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
   
   /**
    * Creates all registered {@link IPreferenceListener}.
    * @return The registered {@link IPreferenceListener}.
    */
   public static List<IPreferenceListener> createListener() {
      // Create result list
      List<IPreferenceListener> result = new LinkedList<IPreferenceListener>();
      // Add results registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(LISTENER_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     IPreferenceListener listener = (IPreferenceListener)configElement.createExecutableExtension("class");
                     result.add(listener);
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + LISTENER_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      return result;
   }
}