package org.key_project.sed.core.annotation;

import org.eclipse.swt.graphics.RGB;
import org.key_project.util.bean.IBean;

/**
 * Defines the appearance of an {@link ISEDAnnotation}.
 * @author Martin Hentschel
 */
public interface ISEDAnnotationAppearance extends IBean {
   /**
    * Property {@link #getType()}.
    */
   public static final String PROP_TYPE = "type";
   
   /**
    * Property {@link #isHighlightBackground()}.
    */
   public static final String PROP_HIGHLIGHT_BACKGROUND = "highlightBackground";

   /**
    * Property {@link #getBackgroundColor()}.
    */
   public static final String PROP_BACKGROUND_COLOR = "backgroundColor";

   /**
    * Property {@link #isHighlightForeground()}.
    */
   public static final String PROP_HIGHLIGHT_FOREGROUND = "highlightForeground";

   /**
    * Property {@link #getForegroundColor()}.
    */
   public static final String PROP_FOREGROUND_COLOR = "ForegroundColor";
   
   /**
    * Returns the {@link ISEDAnnotationType} this {@link ISEDAnnotation} belongs to.
    * @return The {@link ISEDAnnotationType} this {@link ISEDAnnotation} belongs to.
    */
   public ISEDAnnotationType getType();

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
    * Defines the custom background highlighting.
    * @param customHighlightBackground {@code null} to disable custom highlighting or the specified value otherwise.
    */
   public void setCustomHighlightBackground(Boolean customHighlightBackground);

   /**
    * Sets the custom background color.
    * @param customBackgroundColor {@code null} to disable custom color or the specified color otherwise.
    */
   public void setCustomBackgroundColor(RGB customBackgroundColor);

   /**
    * Defines the custom foreground highlighting.
    * @param customHighlightForeground {@code null} to disable custom highlighting or the specified value otherwise.
    */
   public void setCustomHighlightForeground(Boolean customHighlightForeground);

   /**
    * Sets the custom foreground color.
    * @param customForegroundColor {@code null} to disable custom color or the specified color otherwise.
    */
   public void setCustomForegroundColor(RGB customForegroundColor);
   
   /**
    * Applies the current appearance on the given {@link ISEDAnnotationAppearance}
    * so that both will look the same.
    * @param appearance The {@link ISEDAnnotationAppearance} to modify.
    */
   public void applyTo(ISEDAnnotationAppearance appearance);
}
