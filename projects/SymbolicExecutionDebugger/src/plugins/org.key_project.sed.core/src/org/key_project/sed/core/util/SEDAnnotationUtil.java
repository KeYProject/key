package org.key_project.sed.core.util;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * Provides utility methods to work with {@link ISEDAnnotation}s.
 * @author Martin Hentschel
 */
public final class SEDAnnotationUtil {
   /**
    * The ID Of the extension point with the annotation types.
    */
   public static final String ANNOTATION_TYPE_EXTENSION_POINT = "org.key_project.sed.core.annotationTypes";

   /**
    * Contains all available {@link ISEDAnnotationType}s.
    */
   private static final List<ISEDAnnotationType> annotationTypes = createAnnotationTypes();
   
   /**
    * Forbid instances.
    */
   private SEDAnnotationUtil() {
   }
   
   /**
    * Returns all available {@link ISEDAnnotationType}s.
    * @return The available {@link ISEDAnnotationType}s.
    */
   public static List<ISEDAnnotationType> getAnnotationtypes() {
      return annotationTypes;
   }

   /**
    * Reads all available {@link ISEDAnnotationType} from the extension point
    * and creates the {@link ISEDAnnotationType} instances.
    * @return The created {@link ISEDAnnotationType} instances.
    */
   private static List<ISEDAnnotationType> createAnnotationTypes() {
      // Create result list
      List<ISEDAnnotationType> types = new LinkedList<ISEDAnnotationType>();
      // Add drivers registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(ANNOTATION_TYPE_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     ISEDAnnotationType type = (ISEDAnnotationType)configElement.createExecutableExtension("class");
                     types.add(type);
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + ANNOTATION_TYPE_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      return Collections.unmodifiableList(types);
   }

   /**
    * Returns the {@link ISEDAnnotationType} with the given ID.
    * @param typeId The ID of the requested {@link ISEDAnnotationType}.
    * @return The found {@link ISEDAnnotationType} with the given ID or {@code null} if not available.
    */
   public static ISEDAnnotationType getAnnotationtype(final String typeId) {
      return CollectionUtil.search(annotationTypes, new IFilter<ISEDAnnotationType>() {
         @Override
         public boolean select(ISEDAnnotationType element) {
            return ObjectUtil.equals(element.getTypeId(), typeId);
         }
      });
   }

   /**
    * Initializes the given {@link ISEDDebugNode} with annotations.
    * @param node The {@link ISEDDebugNode} to initialize.
    */
   public static void initializeAnnotations(ISEDDebugNode node) throws DebugException {
      if (node != null) {
         ISEDDebugTarget target = node.getDebugTarget();
         if (target != null) {
            ISEDAnnotation[] annotations = target.getRegisteredAnnotations();
            for (ISEDAnnotation annotation : annotations) {
               annotation.getType().initializeNode(node, annotation);
            }
         }
      }
   }
}
