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

package de.hentschel.visualdbc.datasource.ui.util;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.key_project.util.java.ObjectUtil;

import de.hentschel.visualdbc.datasource.ui.setting.ISettingControl;

/**
 * Provides static methods to work with setting controls.
 * @author Martin Hentschel
 */
public final class SettingControlUtil {
   /**
    * ID of the used extension point.
    */
   public static final String SETTING_CONTROL_EXTENSION_POINT = "de.hentschel.visualdbc.dataSource.ui.settingControls";
   
   /**
    * Forbid instances.
    */
   private SettingControlUtil() {
   }
   
   /**
    * Creates a new {@link ISettingControl} for the given ID.
    * @return The created {@link ISettingControl} or {@code null} if no one was registered for the given ID.
    */
   public static ISettingControl createSettingControl(String id) {
      // Add setting controls registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(SETTING_CONTROL_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  if (ObjectUtil.equals(id, configElement.getAttribute("id"))) {
                     try {
                        return (ISettingControl)configElement.createExecutableExtension("class");
                     }
                     catch (Exception e) {
                        LogUtil.getLogger().logError(e);
                     }
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + SETTING_CONTROL_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      return null;
   }
}