package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * The default implementation of {@link ISEDAnnotationLink}.
 * @author Martin Hentschel
 */
public class DefaultSEDAnnotationLink extends AbstractSEDAnnotationLink {
   /**
    * Constructor.
    * @param source The source {@link ISEDAnnotation}.
    * @param target The target {@link ISEDDebugNode}.
    */
   public DefaultSEDAnnotationLink(ISEDAnnotation source, ISEDDebugNode target) {
      super(source, target);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDelete() {
      return false;
   }
}
