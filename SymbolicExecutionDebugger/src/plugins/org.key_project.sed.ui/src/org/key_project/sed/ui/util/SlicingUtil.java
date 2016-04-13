package org.key_project.sed.ui.util;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.key_project.sed.core.slicing.ISESlicer;
import org.key_project.sed.ui.slicing.ISlicingSettingsControlFactory;

/**
 * Provides static methods for slicing.
 * @author Martin Hentschel
 */
public final class SlicingUtil {
   /**
    * The name of the slicing factory extension point.
    */
   public static final String FACTORY_EXTENSION_POINT = "org.key_project.sed.ui.slicingSettingsControlFactories";

   /**
    * Forbid instances.
    */
   private SlicingUtil() {
   }

   /**
    * Returns an {@link ISlicingSettingsControlFactory} compatible to the given {@link ISESlicer}.
    * @param slicer The {@link ISESlicer} for which an {@link ISlicingSettingsControlFactory} is needed.
    * @return The created {@link ISlicingSettingsControlFactory} or {@code null} if none is available.
    */
   public static ISlicingSettingsControlFactory createSlicingSettingsControlFactory(ISESlicer slicer) {
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(FACTORY_EXTENSION_POINT);
         if (point != null) {
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     ISlicingSettingsControlFactory factory = (ISlicingSettingsControlFactory)configElement.createExecutableExtension("class");
                     if (factory != null && factory.isSlicerSupported(slicer)) {
                        return factory;
                     }
                     else {
                        LogUtil.getLogger().logWarning("Driver registered with empty ID.");
                     }
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + FACTORY_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      return null;
   }
}
