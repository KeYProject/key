package org.key_project.sed.ui.provider;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.event.ISEDAnnotationListener;
import org.key_project.sed.core.model.event.SEDAnnotationEvent;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * An {@link IStructuredContentProvider} which shows the registered 
 * {@link ISEDAnnotation}s of an {@link ISEDDebugTarget}. 
 * @author Martin Hentschel
 */
public class AnnotationContentProvider implements IStructuredContentProvider {
   /**
    * The {@link Viewer} in which this provider is used.
    */
   private Viewer viewer;
   
   /**
    * The currently shown and observed {@link ISEDDebugTarget}.
    */
   private ISEDDebugTarget target;
   
   /**
    * Listens for changes on {@link #target}.
    */
   private final ISEDAnnotationListener listener = new ISEDAnnotationListener() {
      @Override
      public void annotationRegistered(SEDAnnotationEvent e) {
         handleAnnotationRegistered(e);
      }
      
      @Override
      public void annotationUnregistered(SEDAnnotationEvent e) {
         handleAnnotationUnregistered(e);
      }

      @Override
      public void annotationMoved(SEDAnnotationEvent e) {
         handleAnnotationMoved(e);
      }
   };
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      this.viewer = viewer;
      if (this.target != null) {
         this.target.removeAnnotationListener(listener);
      }
      if (newInput instanceof ISEDDebugTarget) {
         this.target = (ISEDDebugTarget)newInput;
         this.target.addAnnotationListener(listener);
      }
      else {
         this.target = null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotation[] getElements(Object inputElement) {
      if (inputElement instanceof ISEDDebugTarget) {
         return ((ISEDDebugTarget) inputElement).getRegisteredAnnotations();
      }
      else {
         return new ISEDAnnotation[0];
      }
   }

   /**
    * When a new annotation is registered.
    * @param e The event.
    */
   protected void handleAnnotationRegistered(SEDAnnotationEvent e) {
      SWTUtil.refresh(viewer);
   }

   /**
    * When an existing annotation is unregistered.
    * @param e The event.
    */
   protected void handleAnnotationUnregistered(SEDAnnotationEvent e) {
      SWTUtil.refresh(viewer);
   }

   /**
    * When an existing annotation has moved.
    * @param e The event.
    */
   protected void handleAnnotationMoved(SEDAnnotationEvent e) {
      SWTUtil.refresh(viewer);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      this.viewer = null;
      if (this.target != null) {
         this.target.removeAnnotationListener(listener);
         this.target = null;
      }
   }
}
