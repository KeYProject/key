package org.key_project.sed.core.annotation.impl;

import org.eclipse.core.runtime.Assert;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.util.bean.Bean;

/**
 * Provides the basic functionality of {@link ISEDAnnotationLink}s.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDAnnotationLink extends Bean implements ISEDAnnotationLink {
   /**
    * The source {@link ISEDAnnotation}.
    */
   private final ISEDAnnotation source;
   
   /**
    * The target {@link ISEDDebugNode}.
    */
   private final ISEDDebugNode target;

   /**
    * Constructor.
    * @param source The source {@link ISEDAnnotation}.
    * @param target The target {@link ISEDDebugNode}.
    */
   public AbstractSEDAnnotationLink(ISEDAnnotation source, ISEDDebugNode target) {
      Assert.isNotNull(source);
      Assert.isNotNull(target);
      this.source = source;
      this.target = target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotation getSource() {
      return source;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode getTarget() {
      return target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void delete() {
      target.removeAnnotationLink(this);
   }
}
