package org.key_project.sed.core.annotation.impl;

import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEAnnotationAppearance;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.util.bean.Bean;

/**
 * Provides the basic functionality of {@link ISEAnnotationAppearance}s.
 * @author Martin Hentschel
 */
public abstract class AbstractSEAnnotationAppearance extends Bean implements ISEAnnotationAppearance {
   /**
    * The type of this annotation.
    */
   private final ISEAnnotationType type;
   
   /**
    * The custom background highlighting.
    */
   private Boolean customHighlightBackground;

   /**
    * The custom background color.
    */
   private RGB customBackgroundColor;
   
   /**
    * The custom foreground highlighting.
    */
   private Boolean customHighlightForeground;

   /**
    * The custom foreground color.
    */
   private RGB customForegroundColor;
   
   /**
    * Constructor.
    * @param type The type of this annotation.
    */
   public AbstractSEAnnotationAppearance(ISEAnnotationType type) {
      Assert.isNotNull(type);
      this.type = type;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotationType getType() {
      return type;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isHighlightBackground() {
      if (customHighlightBackground != null) {
         return customHighlightBackground.booleanValue();
      }
      else {
         return type.isHighlightBackground();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RGB getBackgroundColor() {
      if (customBackgroundColor != null) {
         return customBackgroundColor;
      }
      else {
         return type.getBackgroundColor();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isHighlightForeground() {
      if (customHighlightForeground != null) {
         return customHighlightForeground.booleanValue();
      }
      else {
         return type.isHighlightForeground();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RGB getForegroundColor() {
      if (customForegroundColor != null) {
         return customForegroundColor;
      }
      else {
         return type.getForegroundColor();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setCustomHighlightBackground(Boolean customHighlightBackground) {
      boolean oldValue = isHighlightBackground();
      this.customHighlightBackground = customHighlightBackground;
      firePropertyChange(PROP_HIGHLIGHT_BACKGROUND, oldValue, isHighlightBackground());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setCustomBackgroundColor(RGB customBackgroundColor) {
      RGB oldValue = getBackgroundColor();
      this.customBackgroundColor = customBackgroundColor;
      firePropertyChange(PROP_BACKGROUND_COLOR, oldValue, getBackgroundColor());
   }

   /**
    * {@inheritDoc}
    */
   @Override   
   public void setCustomHighlightForeground(Boolean customHighlightForeground) {
      boolean oldValue = isHighlightForeground();
      this.customHighlightForeground = customHighlightForeground;
      firePropertyChange(PROP_HIGHLIGHT_FOREGROUND, oldValue, isHighlightForeground());
   }

   /**
    * {@inheritDoc}
    */
   @Override   
   public void setCustomForegroundColor(RGB customForegroundColor) {
      RGB oldValue = getForegroundColor();
      this.customForegroundColor = customForegroundColor;
      firePropertyChange(PROP_FOREGROUND_COLOR, oldValue, getForegroundColor());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void applyTo(ISEAnnotationAppearance appearance) {
      if (appearance != null) {
         appearance.setCustomBackgroundColor(customBackgroundColor);
         appearance.setCustomForegroundColor(customForegroundColor);
         appearance.setCustomHighlightBackground(customHighlightBackground);
         appearance.setCustomHighlightForeground(customHighlightForeground);
      }
   }
}
