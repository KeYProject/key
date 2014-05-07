package org.key_project.sed.core.annotation.impl;

import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.util.SEDPreferenceUtil;

/**
 * Provides some default implementations of {@link ISEDAnnotationType}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDAnnotationType implements ISEDAnnotationType {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isHighlightBackground() {
      return SEDPreferenceUtil.isAnnotationTypeHighlightBackground(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RGB getBackgroundColor() {
      return SEDPreferenceUtil.getAnnotationTypeBackgroundColor(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isHighlightForeground() {
      return SEDPreferenceUtil.isAnnotationTypeHighlightForeground(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RGB getForegroundColor() {
      return SEDPreferenceUtil.getAnnotationTypeForegroundColor(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String[] getAdditionalLinkColumns() {
      return null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getAdditionalLinkColumnValue(int index, ISEDAnnotationLink link) {
      return null;
   }
}
