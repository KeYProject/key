package org.key_project.sed.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.event.ISEAnnotationLinkListener;
import org.key_project.sed.core.annotation.event.SEAnnotationLinkEvent;
import org.key_project.util.eclipse.swt.viewer.AbstractLabelProvider;

/**
 * An {@link ITableLabelProvider} which shows the available 
 * {@link ISEAnnotationLink}s of an {@link ISEAnnotation}. 
 * @author Martin Hentschel
 */
public class AnnotationAnnotationLinkLabelProvider extends AbstractLabelProvider implements ITableLabelProvider {
   /**
    * The {@link ISEAnnotation} which provides the shown {@link ISEAnnotationLink}s.
    */
   private final ISEAnnotation annotation;
   
   /**
    * Listens for changes on {@link #annotation}.
    */
   private final ISEAnnotationLinkListener annotationListener = new ISEAnnotationLinkListener() {
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
    * Observes {@link ISEAnnotationLink}s.
    */
   private final PropertyChangeListener linksListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handlePropertyChange(evt);
      }
   };
   
   /**
    * The used {@link IDebugModelPresentation} to compute text and images.
    */
   private final IDebugModelPresentation debugModelPresentation = DebugUITools.newDebugModelPresentation();
   
   /**
    * Constructor.
    * @param annotation The {@link ISEAnnotation} which provides the shown {@link ISEAnnotationLink}s.
    */
   public AnnotationAnnotationLinkLabelProvider(ISEAnnotation annotation) {
      Assert.isNotNull(annotation);
      this.annotation = annotation;
      this.annotation.addAnnotationLinkListener(annotationListener);
      for (ISEAnnotationLink link : annotation.getLinks()) {
         link.addPropertyChangeListener(linksListener);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getColumnImage(Object element, int columnIndex) {
      if (element instanceof ISEAnnotationLink) {
         ISEAnnotationLink link = (ISEAnnotationLink)element;
         if (columnIndex == 0) {
            return debugModelPresentation.getImage(link.getTarget());
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getColumnText(Object element, int columnIndex) {
      if (element instanceof ISEAnnotationLink) {
         ISEAnnotationLink link = (ISEAnnotationLink)element;
         if (columnIndex == 0) {
            return debugModelPresentation.getText(link.getTarget());
         }
         else {
            return annotation.getType().getAdditionalLinkColumnValue(columnIndex - 1, link);
         }
      }
      else {
         return null;
      }
   }

   /**
    * When a new annotation link is added.
    * @param e The event.
    */
   protected void handleAnnotationLinkAdded(SEAnnotationLinkEvent e) {
      e.getLink().addPropertyChangeListener(linksListener);
   }

   /**
    * When an existing annotation link is removed.
    * @param e The event.
    */
   protected void handleAnnotationLinkRemoved(SEAnnotationLinkEvent e) {
      e.getLink().removePropertyChangeListener(linksListener);
   }

   /**
    * When an {@link ISEAnnotationLink} has changed.
    * @param evt The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent evt) {
      fireLabelProviderChangedThreadSave(new LabelProviderChangedEvent(this, evt.getSource()));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      annotation.removeAnnotationLinkListener(annotationListener);
      for (ISEAnnotationLink link : annotation.getLinks()) {
         link.removePropertyChangeListener(linksListener);
      }
      if (debugModelPresentation != null) {
         debugModelPresentation.dispose();
      }
   }
}
