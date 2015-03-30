package org.key_project.sed.core.model.event;

import java.util.EventListener;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;

/**
 * Listens for changes on an {@link ISEDDebugTarget}.
 * @author Martin Hentschel
 */
public interface ISEDAnnotationListener extends EventListener {
   /**
    * When a new {@link ISEDAnnotation} was added via
    * {@link ISEDDebugTarget#registerAnnotation(ISEDAnnotation)}.
    * @param e The event.
    */   
   public void annotationRegistered(SEDAnnotationEvent e);

   /**
    * When an existing {@link ISEDAnnotation} was removed via
    * {@link ISEDDebugTarget#unregisterAnnotation(ISEDAnnotation)}.
    * @param e The event.
    */  
   public void annotationUnregistered(SEDAnnotationEvent e);
   
   /**
    * When an existing {@link ISEDAnnotation} was moved via
    * {@link ISEDDebugTarget#moveRegisteredAnnotation(ISEDAnnotation, int)}.
    * @param e The event.
    */
   public void annotationMoved(SEDAnnotationEvent e);
}
