package org.key_project.sed.core.model.event;

import java.util.EventObject;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;

/**
 * An event thrown by an {@link ISEDDebugTarget} and observed via
 * {@link ISEDAnnotationListener}.
 * @author Martin Hentschel
 */
public class SEDAnnotationEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -4406013621820054539L;

   /**
    * The added, moved or removed {@link ISEDAnnotation}.
    */
   private final ISEDAnnotation annotation;
   
   /**
    * Constructor.
    * @param source The modified {@link ISEDDebugTarget}.
    * @param annotation The added, moved or removed {@link ISEDAnnotation}.
    */
   public SEDAnnotationEvent(ISEDDebugTarget source, ISEDAnnotation annotation) {
      super(source);
      this.annotation = annotation;
   }

   /**
    * Returns the added, moved or removed {@link ISEDAnnotation}.
    * @return The added, moved or removed {@link ISEDAnnotation}.
    */
   public ISEDAnnotation getAnnotation() {
      return annotation;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugTarget getSource() {
      return (ISEDDebugTarget)super.getSource();
   }
}
