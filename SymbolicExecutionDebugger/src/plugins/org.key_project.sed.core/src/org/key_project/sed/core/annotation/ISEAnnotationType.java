package org.key_project.sed.core.annotation;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.impl.AbstractSEAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.util.SEAnnotationUtil;

/**
 * <p>
 * An annotation type defines default values of {@link ISEAnnotation}s and
 * provides the functionality to instantiate and to work with {@link ISEAnnotation}.
 * </p>
 * <p>
 * Implementations should subclass from {@link AbstractSEAnnotationType}.
 * </p>
 * <p>
 * Implementations are registered via extension point 
 * {@link SEAnnotationUtil#ANNOTATION_TYPE_EXTENSION_POINT} and can be
 * accessed programmatically via their unique id ({@link #getTypeId()}) passed
 * to {@link SEAnnotationUtil#getAnnotationtype(String)} or in general via
 * {@link SEAnnotationUtil#getAnnotationtypes()}.
 * </p>
 * @author Martin Hentschel
 * @see ISEAnnotation
 * @see ISEAnnotationLink
 */
public interface ISEAnnotationType {
   /**
    * Returns a unique annotation type ID.
    * @return The unique annotation type ID.
    */
   public String getTypeId();
   
   /**
    * Returns the name of this annotation type.
    * @return The name of this annotation type.
    */
   public String getName();

   /**
    * Checks if the background color is highlighted.
    * @return {@code true} highlight, {@code false} do nothing.
    */
   public boolean isHighlightBackground();
   
   /**
    * Returns the background color.
    * @return The background color or {@code null} if not defined.
    */
   public RGB getBackgroundColor();

   /**
    * Checks if the foreground color is highlighted.
    * @return {@code true} highlight, {@code false} do nothing.
    */
   public boolean isHighlightForeground();
   
   /**
    * Returns the foreground color.
    * @return The foreground color or {@code null} if not defined.
    */
   public RGB getForegroundColor();

   /**
    * Checks if the background color is highlighted by default.
    * @return {@code true} highlight, {@code false} do nothing.
    */
   public boolean isDefaultHighlightBackground();
   
   /**
    * Returns the default background color.
    * @return The background color or {@code null} if not defined.
    */
   public RGB getDefaultBackgroundColor();

   /**
    * Checks if the foreground color is highlighted by default.
    * @return {@code true} highlight, {@code false} do nothing.
    */
   public boolean isDefaultHighlightForeground();
   
   /**
    * Returns the default foreground color.
    * @return The foreground color or {@code null} if not defined.
    */
   public RGB getDefaultForegroundColor();
   
   /**
    * Creates a new {@link ISEAnnotation} of this type.
    * @return The newly created {@link ISEAnnotation}.
    */
   public ISEAnnotation createAnnotation();
   
   /**
    * Creates a new {@link ISEAnnotationLink} to the given {@link ISENode}.
    * @param source The source {@link ISEAnnotation} to link from.
    * @param target The target {@link ISENode} to link to.
    * @return The created {@link ISEAnnotationLink}.
    */
   public ISEAnnotationLink createLink(ISEAnnotation source, ISENode target);
   
   /**
    * Returns some optional additional link columns of the given {@link ISEAnnotation}.
    * @param annotation The {@link ISEAnnotation} to show.
    * @return Additional link columns or {@code null} if not available.
    */
   public String[] getAdditionalLinkColumns(ISEAnnotation annotation);
   
   /**
    * Returns the value of the given {@link ISENode} 
    * shown in the additional column with the given index.
    * @param index The index of the additional column.
    * @param link The {@link ISEAnnotationLink} to get its value.
    * @return The text to show.
    */
   public String getAdditionalLinkColumnValue(int index, ISEAnnotationLink link);
   
   /**
    * Saves the specific {@link ISEAnnotation} content as {@link String}.
    * @param annotation The {@link ISEAnnotation} to save.
    * @return The specific {@link ISEAnnotation} content as {@link String}.
    */
   public String saveAnnotation(ISEAnnotation annotation);
   
   /**
    * Restores the saved content on the given {@link ISEAnnotation}.
    * @param annotation The {@link ISEAnnotation} to restore its content.
    * @param savedContent The content to restore.
    */
   public void restoreAnnotation(ISEAnnotation annotation, String savedContent);
   
   /**
    * Saves the specific {@link ISEAnnotationLink} content as {@link String}.
    * @param link The {@link ISEAnnotationLink} to save.
    * @return The specific {@link ISEAnnotationLink} content as {@link String}.
    */
   public String saveAnnotationLink(ISEAnnotationLink link);
   
   /**
    * Restores the saved content on the given {@link ISEAnnotationLink}.
    * @param link The {@link ISEAnnotationLink} to restore its content.
    * @param savedContent The content to restore.
    */
   public void restoreAnnotationLink(ISEAnnotationLink link, String savedContent);

   /**
    * This method is called when a new {@link ISENode} is created
    * to may initialize it with the given {@link ISEAnnotation}.
    * @param node The {@link ISENode} to initialize.
    * @param annotation The {@link ISEAnnotation} which might be added to the {@link ISENode} or not.
    */
   public void initializeNode(ISENode node, ISEAnnotation annotation) throws DebugException;
}
