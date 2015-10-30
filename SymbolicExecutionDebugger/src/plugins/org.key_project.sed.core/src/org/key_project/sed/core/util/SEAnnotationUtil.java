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
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * Provides utility methods to work with {@link ISEAnnotation}s.
 * @author Martin Hentschel
 */
public final class SEAnnotationUtil {
   /**
    * The ID Of the extension point with the annotation types.
    */
   public static final String ANNOTATION_TYPE_EXTENSION_POINT = "org.key_project.sed.core.annotationTypes";

   /**
    * Contains all available {@link ISEAnnotationType}s.
    */
   private static final List<ISEAnnotationType> annotationTypes = createAnnotationTypes();
   
   /**
    * Forbid instances.
    */
   private SEAnnotationUtil() {
   }
   
   /**
    * Returns all available {@link ISEAnnotationType}s.
    * @return The available {@link ISEAnnotationType}s.
    */
   public static List<ISEAnnotationType> getAnnotationtypes() {
      return annotationTypes;
   }

   /**
    * Reads all available {@link ISEAnnotationType} from the extension point
    * and creates the {@link ISEAnnotationType} instances.
    * @return The created {@link ISEAnnotationType} instances.
    */
   private static List<ISEAnnotationType> createAnnotationTypes() {
      // Create result list
      List<ISEAnnotationType> types = new LinkedList<ISEAnnotationType>();
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
                     ISEAnnotationType type = (ISEAnnotationType)configElement.createExecutableExtension("class");
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
    * Returns the {@link ISEAnnotationType} with the given ID.
    * @param typeId The ID of the requested {@link ISEAnnotationType}.
    * @return The found {@link ISEAnnotationType} with the given ID or {@code null} if not available.
    */
   public static ISEAnnotationType getAnnotationtype(final String typeId) {
      return CollectionUtil.search(annotationTypes, new IFilter<ISEAnnotationType>() {
         @Override
         public boolean select(ISEAnnotationType element) {
            return ObjectUtil.equals(element.getTypeId(), typeId);
         }
      });
   }

   /**
    * Initializes the given {@link ISENode} with annotations.
    * @param node The {@link ISENode} to initialize.
    */
   public static void initializeAnnotations(ISENode node) throws DebugException {
      if (node != null) {
         ISEDebugTarget target = node.getDebugTarget();
         if (target != null) {
            ISEAnnotation[] annotations = target.getRegisteredAnnotations();
            for (ISEAnnotation annotation : annotations) {
               annotation.getType().initializeNode(node, annotation);
            }
         }
      }
   }
}
