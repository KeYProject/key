package org.key_project.sed.core.annotation.impl;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.util.SEDPreferenceUtil;

/**
 * Provides some default implementations of {@link ISEAnnotationType}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEAnnotationType implements ISEAnnotationType {
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
   public String[] getAdditionalLinkColumns(ISEAnnotation annotation) {
      return null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getAdditionalLinkColumnValue(int index, ISEAnnotationLink link) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String saveAnnotation(ISEAnnotation annotation) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotation(ISEAnnotation annotation, String savedContent) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String saveAnnotationLink(ISEAnnotationLink link) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotationLink(ISEAnnotationLink link, String savedContent) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeNode(ISENode node, ISEAnnotation annotation) throws DebugException {
   }
}
