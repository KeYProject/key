package org.key_project.sed.ui.provider;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.event.ISEAnnotationListener;
import org.key_project.sed.core.model.event.SEAnnotationEvent;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * An {@link IStructuredContentProvider} which shows the registered 
 * {@link ISEAnnotation}s of an {@link ISEDebugTarget}. 
 * @author Martin Hentschel
 */
public class AnnotationContentProvider implements IStructuredContentProvider {
   /**
    * The {@link Viewer} in which this provider is used.
    */
   private Viewer viewer;
   
   /**
    * The currently shown and observed {@link ISEDebugTarget}.
    */
   private ISEDebugTarget target;
   
   /**
    * Listens for changes on {@link #target}.
    */
   private final ISEAnnotationListener listener = new ISEAnnotationListener() {
      @Override
      public void annotationRegistered(SEAnnotationEvent e) {
         handleAnnotationRegistered(e);
      }
      
      @Override
      public void annotationUnregistered(SEAnnotationEvent e) {
         handleAnnotationUnregistered(e);
      }

      @Override
      public void annotationMoved(SEAnnotationEvent e) {
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
      if (newInput instanceof ISEDebugTarget) {
         this.target = (ISEDebugTarget)newInput;
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
   public ISEAnnotation[] getElements(Object inputElement) {
      if (inputElement instanceof ISEDebugTarget) {
         return ((ISEDebugTarget) inputElement).getRegisteredAnnotations();
      }
      else {
         return new ISEAnnotation[0];
      }
   }

   /**
    * When a new annotation is registered.
    * @param e The event.
    */
   protected void handleAnnotationRegistered(SEAnnotationEvent e) {
      SWTUtil.refresh(viewer);
   }

   /**
    * When an existing annotation is unregistered.
    * @param e The event.
    */
   protected void handleAnnotationUnregistered(SEAnnotationEvent e) {
      SWTUtil.refresh(viewer);
   }

   /**
    * When an existing annotation has moved.
    * @param e The event.
    */
   protected void handleAnnotationMoved(SEAnnotationEvent e) {
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
