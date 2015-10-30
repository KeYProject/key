package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.model.ISENode;

/**
 * An {@link ISEAnnotationLink} which represents a search result.
 * @author Martin Hentschel
 */
public class SliceAnnotationLink extends AbstractSEAnnotationLink {
   /**
    * Constructor.
    * @param source The source {@link ISEAnnotation}.
    * @param target The target {@link ISENode}.
    */
   public SliceAnnotationLink(ISEAnnotation source, ISENode target) {
      super(source, target);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDelete() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return getSource().toString();
   }
}
