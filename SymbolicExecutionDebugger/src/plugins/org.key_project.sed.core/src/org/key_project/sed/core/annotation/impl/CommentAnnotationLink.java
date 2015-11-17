package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.model.ISENode;

/**
 * An {@link ISEAnnotationLink} which can be extended by comments.
 * @author Martin Hentschel
 */
public class CommentAnnotationLink extends AbstractSEAnnotationLink {
   /**
    * Property {@link #getComment()}.
    */
   public static final String PROP_COMMENT = "comment";
   
   /**
    * The comments.
    */
   private String comment;
   
   /**
    * Constructor.
    * @param source The source {@link ISEAnnotation}.
    * @param target The target {@link ISENode}.
    */
   public CommentAnnotationLink(ISEAnnotation source, ISENode target) {
      super(source, target);
   }

   /**
    * Returns the comment.
    * @return The comment.
    */
   public String getComment() {
      return comment;
   }

   /**
    * Sets the comment.
    * @param comment The comment to set.
    */
   public void setComment(String comment) {
      String oldValue = getComment();
      this.comment = comment;
      firePropertyChange(PROP_COMMENT, oldValue, getComment());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDelete() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void delete() {
      // Remove link
      super.delete();
      // Remove annotation if no links are available
      if (!getSource().hasLinks()) {
         getTarget().getDebugTarget().unregisterAnnotation(getSource());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return getComment();
   }
}
