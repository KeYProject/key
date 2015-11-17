package org.key_project.sed.core.model.event;

import java.util.EventObject;

import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;

/**
 * An event thrown by an {@link ISEDebugTarget} and observed via
 * {@link ISEAnnotationListener}.
 * @author Martin Hentschel
 */
public class SEAnnotationEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -4406013621820054539L;

   /**
    * The added, moved or removed {@link ISEAnnotation}.
    */
   private final ISEAnnotation annotation;
   
   /**
    * Constructor.
    * @param source The modified {@link ISEDebugTarget}.
    * @param annotation The added, moved or removed {@link ISEAnnotation}.
    */
   public SEAnnotationEvent(ISEDebugTarget source, ISEAnnotation annotation) {
      super(source);
      this.annotation = annotation;
   }

   /**
    * Returns the added, moved or removed {@link ISEAnnotation}.
    * @return The added, moved or removed {@link ISEAnnotation}.
    */
   public ISEAnnotation getAnnotation() {
      return annotation;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDebugTarget getSource() {
      return (ISEDebugTarget)super.getSource();
   }
}
