package org.key_project.sed.core.annotation.impl;

import org.eclipse.core.runtime.Assert;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.impl.AbstractSEDebugElement;
import org.key_project.util.bean.Bean;

/**
 * Provides the basic functionality of {@link ISEAnnotationLink}s.
 * @author Martin Hentschel
 */
public abstract class AbstractSEAnnotationLink extends Bean implements ISEAnnotationLink {
   /**
    * The unique ID.
    */
   private String id;
   
   /**
    * The source {@link ISEAnnotation}.
    */
   private final ISEAnnotation source;
   
   /**
    * The target {@link ISENode}.
    */
   private final ISENode target;

   /**
    * Constructor.
    * @param source The source {@link ISEAnnotation}.
    * @param target The target {@link ISENode}.
    */
   public AbstractSEAnnotationLink(ISEAnnotation source, ISENode target) {
      Assert.isNotNull(source);
      Assert.isNotNull(target);
      this.source = source;
      this.target = target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotation getSource() {
      return source;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISENode getTarget() {
      return target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void delete() {
      target.removeAnnotationLink(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getId() {
      if (id == null) {
         synchronized (this) {
            if (id == null) {
               id = AbstractSEDebugElement.computeNewId();
            }
         }
      }
      return id;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setId(String id) {
      Assert.isTrue(this.id == null, "Can't change an already existing ID.");
      this.id = id;
   }
}
