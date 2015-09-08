package org.key_project.javaeditor.util;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.key_project.javaeditor.outline.IOutlineModifier;

/**
 * Util to call all Extensions of the {@link IOutlineModifier}.
 * @author Martin Hentschel, Timm Lippert
 *
 */

public final class ExtendableOutlineUtil {
    /**
     * ID of extension point which provides {@link IOutlineModifier} implementations.
     */
    private static final String JAVA_OUTLINE_EXTENSION_POINT = "org.key_project.javaeditor.javaOutlineExtension";

    /**
     * No instances allowed.
     */
    private ExtendableOutlineUtil() {
    }
    
    /**
     * Reads all available {@link IOutlineModifier} from the extension point
     * which are enabled according to {@link PreferenceUtil#isExtensionEnabled(String)}.
     * @return The created {@link IOutlineModifier} instances.
     */
    public static IOutlineModifier[] createEnabledJavaExtensions() {
       // Create result list
       List<IOutlineModifier> result = new LinkedList<IOutlineModifier>();
       // Add results registered by the extension point
       IExtensionRegistry registry = Platform.getExtensionRegistry();
       if (registry != null) {
          IExtensionPoint point = registry.getExtensionPoint(JAVA_OUTLINE_EXTENSION_POINT);
          if (point != null) {
             // Analyze the extension point
             IExtension[] extensions = point.getExtensions();
             for (IExtension extension : extensions) {
                IConfigurationElement[] configElements = extension.getConfigurationElements();
                for (IConfigurationElement configElement : configElements) {
                   try {
                       IOutlineModifier javaExtension = (IOutlineModifier)configElement.createExecutableExtension("class");
                       result.add(javaExtension);
                   }
                   catch (Exception e) {
                      LogUtil.getLogger().logError(e);
                   }
                }
             }
          }
          else {
             LogUtil.getLogger().logError("Extension point \"" + JAVA_OUTLINE_EXTENSION_POINT + "\" doesn't exist.");
          }
       }
       else {
          LogUtil.getLogger().logError("Extension point registry is not loaded.");
       }
       return result.toArray(new IOutlineModifier[result.size()]);
    }
}