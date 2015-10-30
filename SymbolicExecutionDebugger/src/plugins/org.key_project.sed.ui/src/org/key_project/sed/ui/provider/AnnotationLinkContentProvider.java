package org.key_project.sed.ui.provider;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.event.ISEAnnotationLinkListener;
import org.key_project.sed.core.model.event.SEAnnotationEvent;
import org.key_project.sed.core.model.event.SEAnnotationLinkEvent;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * An {@link IStructuredContentProvider} which shows the registered 
 * {@link ISEAnnotationLink}s of an {@link ISENode}. 
 * @author Martin Hentschel
 */
public class AnnotationLinkContentProvider implements IStructuredContentProvider {
   /**
    * The {@link Viewer} in which this provider is used.
    */
   private Viewer viewer;
   
   /**
    * The currently shown and observed {@link ISENode}.
    */
   private ISENode target;
   
   /**
    * Listens for changes on {@link #target}.
    */
   private final ISEAnnotationLinkListener listener = new ISEAnnotationLinkListener() {
      @Override
      public void annotationLinkAdded(SEAnnotationLinkEvent e) {
         handleAnnotationLinkAdded(e);
      }
      
      @Override
      public void annotationLinkRemoved(SEAnnotationLinkEvent e) {
         handleAnnotationLinkRemoved(e);
      }
   };
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      this.viewer = viewer;
      if (this.target != null) {
         this.target.removeAnnotationLinkListener(listener);
      }
      if (newInput instanceof ISENode) {
         this.target = (ISENode)newInput;
         this.target.addAnnotationLinkListener(listener);
      }
      else {
         this.target = null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotationLink[] getElements(Object inputElement) {
      if (inputElement instanceof ISENode) {
         return ((ISENode) inputElement).getAnnotationLinks();
      }
      else {
         return new ISEAnnotationLink[0];
      }
   }

   /**
    * When a new annotation link is added.
    * @param e The event.
    */
   protected void handleAnnotationLinkAdded(SEAnnotationLinkEvent e) {
      SWTUtil.refresh(viewer);
   }

   /**
    * When an existing annotation link is removed.
    * @param e The event.
    */
   protected void handleAnnotationLinkRemoved(SEAnnotationLinkEvent e) {
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
         this.target.removeAnnotationLinkListener(listener);
         this.target = null;
      }
   }
}
