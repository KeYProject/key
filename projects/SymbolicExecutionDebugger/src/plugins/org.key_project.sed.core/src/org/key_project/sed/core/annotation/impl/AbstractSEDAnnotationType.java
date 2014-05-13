package org.key_project.sed.core.annotation.impl;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.ISEDDebugNode;
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
   public String[] getAdditionalLinkColumns(ISEDAnnotation annotation) {
      return null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getAdditionalLinkColumnValue(int index, ISEDAnnotationLink link) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String saveAnnotation(ISEDAnnotation annotation) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotation(ISEDAnnotation annotation, String savedContent) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String saveAnnotationLink(ISEDAnnotationLink link) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotationLink(ISEDAnnotationLink link, String savedContent) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeNode(ISEDDebugNode node, ISEDAnnotation annotation) throws DebugException {
   }
}
