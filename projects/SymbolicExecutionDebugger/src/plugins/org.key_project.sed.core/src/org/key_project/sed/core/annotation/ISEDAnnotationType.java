package org.key_project.sed.core.annotation;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.impl.AbstractSEDAnnotationType;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.util.SEDAnnotationUtil;

/**
 * <p>
 * An annotation type defines default values of {@link ISEDAnnotation}s and
 * provides the functionality to instantiate and to work with {@link ISEDAnnotation}.
 * </p>
 * <p>
 * Implementations should subclass from {@link AbstractSEDAnnotationType}.
 * </p>
 * <p>
 * Implementations are registered via extension point 
 * {@link SEDAnnotationUtil#ANNOTATION_TYPE_EXTENSION_POINT} and can be
 * accessed programmatically via their unique id ({@link #getTypeId()}) passed
 * to {@link SEDAnnotationUtil#getAnnotationtype(String)} or in general via
 * {@link SEDAnnotationUtil#getAnnotationtypes()}.
 * </p>
 * @author Martin Hentschel
 * @see ISEDAnnotation
 * @see ISEDAnnotationLink
 */
public interface ISEDAnnotationType {
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
    * Creates a new {@link ISEDAnnotation} of this type.
    * @return The newly created {@link ISEDAnnotation}.
    */
   public ISEDAnnotation createAnnotation();
   
   /**
    * Creates a new {@link ISEDAnnotationLink} to the given {@link ISEDDebugNode}.
    * @param source The source {@link ISEDAnnotation} to link from.
    * @param target The target {@link ISEDDebugNode} to link to.
    * @return The created {@link ISEDAnnotationLink}.
    */
   public ISEDAnnotationLink createLink(ISEDAnnotation source, ISEDDebugNode target);
   
   /**
    * Returns some optional additional link columns of the given {@link ISEDAnnotation}.
    * @param annotation The {@link ISEDAnnotation} to show.
    * @return Additional link columns or {@code null} if not available.
    */
   public String[] getAdditionalLinkColumns(ISEDAnnotation annotation);
   
   /**
    * Returns the value of the given {@link ISEDDebugNode} 
    * shown in the additional column with the given index.
    * @param index The index of the additional column.
    * @param link The {@link ISEDAnnotationLink} to get its value.
    * @return The text to show.
    */
   public String getAdditionalLinkColumnValue(int index, ISEDAnnotationLink link);
   
   /**
    * Saves the specific {@link ISEDAnnotation} content as {@link String}.
    * @param annotation The {@link ISEDAnnotation} to save.
    * @return The specific {@link ISEDAnnotation} content as {@link String}.
    */
   public String saveAnnotation(ISEDAnnotation annotation);
   
   /**
    * Restores the saved content on the given {@link ISEDAnnotation}.
    * @param annotation The {@link ISEDAnnotation} to restore its content.
    * @param savedContent The content to restore.
    */
   public void restoreAnnotation(ISEDAnnotation annotation, String savedContent);
   
   /**
    * Saves the specific {@link ISEDAnnotationLink} content as {@link String}.
    * @param link The {@link ISEDAnnotationLink} to save.
    * @return The specific {@link ISEDAnnotationLink} content as {@link String}.
    */
   public String saveAnnotationLink(ISEDAnnotationLink link);
   
   /**
    * Restores the saved content on the given {@link ISEDAnnotationLink}.
    * @param link The {@link ISEDAnnotationLink} to restore its content.
    * @param savedContent The content to restore.
    */
   public void restoreAnnotationLink(ISEDAnnotationLink link, String savedContent);

   /**
    * This method is called when a new {@link ISEDDebugNode} is created
    * to may initialize it with the given {@link ISEDAnnotation}.
    * @param node The {@link ISEDDebugNode} to initialize.
    * @param annotation The {@link ISEDAnnotation} which might be added to the {@link ISEDDebugNode} or not.
    */
   public void initializeNode(ISEDDebugNode node, ISEDAnnotation annotation) throws DebugException;
}
