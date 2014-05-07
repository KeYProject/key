package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.util.SEDAnnotationUtil;

/**
 * The {@link ISEDAnnotation} representing comments.
 * @author Martin Hentschel
 * @see CommentAnnotationType
 */
public class CommentAnnotation extends AbstractSEDAnnotation {
   /**
    * Constructor.
    */
   public CommentAnnotation() {
      super(SEDAnnotationUtil.getAnnotationtype(CommentAnnotationType.TYPE_ID), false);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDelete(ISEDDebugTarget target) {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "Comments";
   }
}
