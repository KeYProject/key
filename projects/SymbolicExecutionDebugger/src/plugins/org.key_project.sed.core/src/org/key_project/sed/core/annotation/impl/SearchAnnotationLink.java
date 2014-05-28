package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * An {@link ISEDAnnotationLink} which represents a search result.
 * @author Martin Hentschel
 */
public class SearchAnnotationLink extends AbstractSEDAnnotationLink {
   /**
    * Constructor.
    * @param source The source {@link ISEDAnnotation}.
    * @param target The target {@link ISEDDebugNode}.
    */
   public SearchAnnotationLink(ISEDAnnotation source, ISEDDebugNode target) {
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
