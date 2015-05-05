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
import org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * Provides utility methods to work with available {@link IJavaSourceViewerConfigurationExtension}s.
 * @author Martin Hentschel
 */
public final class ExtendableConfigurationUtil {
   /**
    * ID of the used extension point.
    */
   public static final String JAVA_CONFIGURATION_EXTENSIONS_EXTENSION_POINT = "org.key_project.javaeditor.javaConfigurationExtensions";
   
   /**
    * Forbid instances.
    */
   private ExtendableConfigurationUtil() {
   }
   
   /**
    * Reads all available {@link IJavaSourceViewerConfigurationExtension} from the extension point
    * which are enabled according to {@link PreferenceUtil#isExtensionEnabled(String)}.
    * @return The created {@link IJavaSourceViewerConfigurationExtension} instances.
    */
   public static IJavaSourceViewerConfigurationExtension[] createEnabledJavaExtensions() {
      // Create result list
      List<IJavaSourceViewerConfigurationExtension> result = new LinkedList<IJavaSourceViewerConfigurationExtension>();
      // Add results registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(JAVA_CONFIGURATION_EXTENSIONS_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     if (PreferenceUtil.isExtensionEnabled(configElement.getAttribute("id"))) {
                        IJavaSourceViewerConfigurationExtension javaExtension = (IJavaSourceViewerConfigurationExtension)configElement.createExecutableExtension("class");
                        result.add(javaExtension);
                     }
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + JAVA_CONFIGURATION_EXTENSIONS_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      return result.toArray(new IJavaSourceViewerConfigurationExtension[result.size()]);
   }

   /**
    * Returns the {@link ExtensionDescription} with the given ID.
    * @param id The ID of the requested {@link ExtensionDescription}.
    * @return The found {@link ExtensionDescription} or {@code null} if not available.
    */
   public static ExtensionDescription getExtensionDescription(final String id) {
      ExtensionDescription[] descriptions = getExtensionDescriptions();
      return ArrayUtil.search(descriptions, new IFilter<ExtensionDescription>() {
         @Override
         public boolean select(ExtensionDescription element) {
            return ObjectUtil.equals(element.getId(), id);
         }
      });
   }

   /**
    * Returns the available {@link ExtensionDescription}s.
    * @return The available {@link ExtensionDescription}s.
    */
   public static ExtensionDescription[] getExtensionDescriptions() {
      // Create result list
      List<ExtensionDescription> result = new LinkedList<ExtensionDescription>();
      // Add results registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(JAVA_CONFIGURATION_EXTENSIONS_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  result.add(new ExtensionDescription(configElement));
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + JAVA_CONFIGURATION_EXTENSIONS_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      return result.toArray(new ExtensionDescription[result.size()]);
   }
   
   /**
    * An {@link IJavaSourceViewerConfigurationExtension} description.
    * @author Martin Hentschel
    */
   public static final class ExtensionDescription {
      /**
       * The ID.
       */
      private final String id;
      
      /**
       * The name.
       */
      private final String name;
      
      /**
       * The default enabled state.
       */
      private final boolean defaultEnabled;

      /**
       * Constructor.
       * @param configElement The {@link IConfigurationElement} to read values from.
       */
      private ExtensionDescription(IConfigurationElement configElement) {
         this.id = configElement.getAttribute("id");
         this.name = configElement.getAttribute("name");
         this.defaultEnabled = Boolean.parseBoolean(configElement.getAttribute("defaultEnabled"));
      }

      /**
       * Returns the id.
       * @return The id.
       */
      public String getId() {
         return id;
      }

      /**
       * Returns the name.
       * @return The name.
       */
      public String getName() {
         return name;
      }

      /**
       * Returns the default enabled state.
       * @return The default enabled state.
       */
      public boolean isDefaultEnabled() {
         return defaultEnabled;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int hashCode() {
         return ObjectUtil.hashCode(getId());
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean equals(Object obj) {
         if(obj == this) {
            return true;
         }
         if (obj == null || obj.getClass() != getClass() || hashCode() != obj.hashCode()) {
            return false; 
         }
         final ExtensionDescription description = (ExtensionDescription) obj;
         return ObjectUtil.equals(getId(), description.getId());
      }
   }
}
