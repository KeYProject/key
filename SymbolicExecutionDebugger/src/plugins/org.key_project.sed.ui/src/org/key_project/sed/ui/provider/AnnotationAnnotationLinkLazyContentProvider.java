package org.key_project.sed.ui.provider;

import org.eclipse.jface.viewers.ILazyContentProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.event.ISEAnnotationLinkListener;
import org.key_project.sed.core.annotation.event.SEAnnotationLinkEvent;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * An {@link ILazyContentProvider} which shows the available 
 * {@link ISEAnnotationLink}s of an {@link ISEAnnotation}. 
 * @author Martin Hentschel
 */
public class AnnotationAnnotationLinkLazyContentProvider implements ILazyContentProvider {
   /**
    * The {@link TableViewer} in which this provider is used.
    */
   private TableViewer viewer;
   
   /**
    * The currently shown and observed {@link ISEAnnotation}.
    */
   private ISEAnnotation annotation;
   
   /**
    * Listens for changes on {@link #annotation}.
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
      this.viewer = (TableViewer)viewer;
      if (this.annotation != null) {
         this.annotation.removeAnnotationLinkListener(listener);
      }
      if (newInput instanceof ISEAnnotation) {
         this.annotation = (ISEAnnotation)newInput;
         this.annotation.addAnnotationLinkListener(listener);
         this.viewer.setItemCount(this.annotation.countLinks());
      }
      else {
         this.annotation = null;
         this.viewer.setItemCount(0);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateElement(int index) {
      SWTUtil.replace(viewer, annotation.getLinkAt(index), index);
   }

   /**
    * When a new annotation link is added.
    * @param e The event.
    */
   protected void handleAnnotationLinkAdded(SEAnnotationLinkEvent e) {
      SWTUtil.add(viewer, e.getLink());
   }

   /**
    * When an existing annotation link is removed.
    * @param e The event.
    */
   protected void handleAnnotationLinkRemoved(SEAnnotationLinkEvent e) {
      SWTUtil.remove(viewer, e.getLink());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      this.viewer = null;
      if (this.annotation != null) {
         this.annotation.removeAnnotationLinkListener(listener);
         this.annotation = null;
      }
   }
}
