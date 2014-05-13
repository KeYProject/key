package org.key_project.sed.core.annotation.impl;

import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * The {@link ISEDAnnotationType} used for comments.
 * @author Martin Hentschel
 * @see CommentAnnotation
 * @see CommentAnnotationLink
 */
public class CommentAnnotationType extends AbstractSEDAnnotationType {
   /**
    * The ID of this annotation type.
    */
   public static final String TYPE_ID = "org.key_project.sed.core.annotationType.comment";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getTypeId() {
      return TYPE_ID;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Comments";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDefaultHighlightBackground() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RGB getDefaultBackgroundColor() {
      return new RGB(239, 228, 176); // yellow like
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDefaultHighlightForeground() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RGB getDefaultForegroundColor() {
      return new RGB(0, 0, 0); // black
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public CommentAnnotation createAnnotation() {
      return new CommentAnnotation();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public CommentAnnotationLink createLink(ISEDAnnotation source, ISEDDebugNode target) {
      return new CommentAnnotationLink(source, target);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String[] getAdditionalLinkColumns(ISEDAnnotation annotation) {
      Assert.isTrue(annotation instanceof CommentAnnotation);
      return new String[] {((CommentAnnotation)annotation).getCommentType()};
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getAdditionalLinkColumnValue(int index, ISEDAnnotationLink link) {
      if (link instanceof CommentAnnotationLink) {
         if (index == 0) {
            return ((CommentAnnotationLink) link).getComment();
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String saveAnnotation(ISEDAnnotation annotation) {
      Assert.isTrue(annotation instanceof CommentAnnotation);
      return ((CommentAnnotation)annotation).getCommentType();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotation(ISEDAnnotation annotation, String savedContent) {
      Assert.isTrue(annotation instanceof CommentAnnotation);
      ((CommentAnnotation)annotation).setCommentType(savedContent);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String saveAnnotationLink(ISEDAnnotationLink link) {
      Assert.isTrue(link instanceof CommentAnnotationLink);
      return ((CommentAnnotationLink)link).getComment();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotationLink(ISEDAnnotationLink link, String savedContent) {
      Assert.isTrue(link instanceof CommentAnnotationLink);
      ((CommentAnnotationLink)link).setComment(savedContent);
   }
}
