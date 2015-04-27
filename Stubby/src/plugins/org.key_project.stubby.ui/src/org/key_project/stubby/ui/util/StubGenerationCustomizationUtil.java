package org.key_project.stubby.ui.util;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.IJavaProject;
import org.key_project.stubby.ui.customization.IStubGenerationCustomization;

/**
 * Provides utility methods to work with {@link IStubGenerationCustomization}s.
 * @author Martin Hentschel
 */
public class StubGenerationCustomizationUtil {
   /**
    * ID of the used extension point.
    */
   public static final String CUSTOMIZATIONS_EXTENSION_POINT = "org.key_project.stubby.ui.customizations";

   /**
    * Forbid instances.
    */
   private StubGenerationCustomizationUtil() {
   }
   
   /**
    * Creates all registered {@link IStubGenerationCustomization}s.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    * @return The created {@link IStubGenerationCustomization} instances.
    */
   public static List<IStubGenerationCustomization> createCustomizations(IJavaProject javaProject) {
      // Create result list
      List<IStubGenerationCustomization> result = new LinkedList<IStubGenerationCustomization>();
      // Add drivers registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(CUSTOMIZATIONS_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     IStubGenerationCustomization customization = (IStubGenerationCustomization)configElement.createExecutableExtension("class");
                     customization.init(javaProject);
                     result.add(customization);
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + CUSTOMIZATIONS_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      return result;
   }
}
