package org.key_project.sed.ui.provider;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.event.ISEDAnnotationLinkListener;
import org.key_project.sed.core.model.event.SEDAnnotationEvent;
import org.key_project.sed.core.model.event.SEDAnnotationLinkEvent;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * An {@link IStructuredContentProvider} which shows the registered 
 * {@link ISEDAnnotationLink}s of an {@link ISEDDebugNode}. 
 * @author Martin Hentschel
 */
public class AnnotationLinkContentProvider implements IStructuredContentProvider {
   /**
    * The {@link Viewer} in which this provider is used.
    */
   private Viewer viewer;
   
   /**
    * The currently shown and observed {@link ISEDDebugNode}.
    */
   private ISEDDebugNode target;
   
   /**
    * Listens for changes on {@link #target}.
    */
   private final ISEDAnnotationLinkListener listener = new ISEDAnnotationLinkListener() {
      @Override
      public void annotationLinkAdded(SEDAnnotationLinkEvent e) {
         handleAnnotationLinkAdded(e);
      }
      
      @Override
      public void annotationLinkRemoved(SEDAnnotationLinkEvent e) {
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
      if (newInput instanceof ISEDDebugNode) {
         this.target = (ISEDDebugNode)newInput;
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
   public ISEDAnnotationLink[] getElements(Object inputElement) {
      if (inputElement instanceof ISEDDebugNode) {
         return ((ISEDDebugNode) inputElement).getAnnotationLinks();
      }
      else {
         return new ISEDAnnotationLink[0];
      }
   }

   /**
    * When a new annotation link is added.
    * @param e The event.
    */
   protected void handleAnnotationLinkAdded(SEDAnnotationLinkEvent e) {
      SWTUtil.refresh(viewer);
   }

   /**
    * When an existing annotation link is removed.
    * @param e The event.
    */
   protected void handleAnnotationLinkRemoved(SEDAnnotationLinkEvent e) {
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
         this.target.removeAnnotationLinkListener(listener);
         this.target = null;
      }
   }
}
