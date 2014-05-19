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
    * The default comment type.
    */
   public static final String DEFAULT_COMMENT_TYPE = "Comment";

   /**
    * Property {@link #getCommentType()}.
    */
   public static final String PROP_COMMENT_TYPE = "commentType";
   
   /**
    * The type of comments.
    */
   private String commentType = DEFAULT_COMMENT_TYPE;
   
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
    * Returns the type of comments.
    * @return The type of comments.
    */
   public String getCommentType() {
      return commentType;
   }

   /**
    * Sets the type of comments.
    * @param commentType The type of comments to set.
    */
   public void setCommentType(String commentType) {
      String oldValue = getCommentType();
      this.commentType = commentType;
      firePropertyChange(PROP_COMMENT_TYPE, oldValue, getCommentType());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return getCommentType();
   }
}
