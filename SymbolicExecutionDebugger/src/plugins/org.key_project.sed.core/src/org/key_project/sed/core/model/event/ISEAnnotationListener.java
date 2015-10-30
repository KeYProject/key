package org.key_project.sed.core.model.event;

import java.util.EventListener;

import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;

/**
 * Listens for changes on an {@link ISEDebugTarget}.
 * @author Martin Hentschel
 */
public interface ISEAnnotationListener extends EventListener {
   /**
    * When a new {@link ISEAnnotation} was added via
    * {@link ISEDebugTarget#registerAnnotation(ISEAnnotation)}.
    * @param e The event.
    */   
   public void annotationRegistered(SEAnnotationEvent e);

   /**
    * When an existing {@link ISEAnnotation} was removed via
    * {@link ISEDebugTarget#unregisterAnnotation(ISEAnnotation)}.
    * @param e The event.
    */  
   public void annotationUnregistered(SEAnnotationEvent e);
   
   /**
    * When an existing {@link ISEAnnotation} was moved via
    * {@link ISEDebugTarget#moveRegisteredAnnotation(ISEAnnotation, int)}.
    * @param e The event.
    */
   public void annotationMoved(SEAnnotationEvent e);
}
