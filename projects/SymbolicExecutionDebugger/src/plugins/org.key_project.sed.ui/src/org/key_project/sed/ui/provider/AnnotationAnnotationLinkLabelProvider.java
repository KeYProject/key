package org.key_project.sed.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.event.ISEDAnnotationLinkListener;
import org.key_project.sed.core.annotation.event.SEDAnnotationLinkEvent;
import org.key_project.util.eclipse.swt.viewer.AbstractLabelProvider;

/**
 * An {@link ITableLabelProvider} which shows the available 
 * {@link ISEDAnnotationLink}s of an {@link ISEDAnnotation}. 
 * @author Martin Hentschel
 */
public class AnnotationAnnotationLinkLabelProvider extends AbstractLabelProvider implements ITableLabelProvider {
   /**
    * The {@link ISEDAnnotation} which provides the shown {@link ISEDAnnotationLink}s.
    */
   private final ISEDAnnotation annotation;
   
   /**
    * Listens for changes on {@link #annotation}.
    */
   private final ISEDAnnotationLinkListener annotationListener = new ISEDAnnotationLinkListener() {
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
    * Observes {@link ISEDAnnotationLink}s.
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
    * @param annotation The {@link ISEDAnnotation} which provides the shown {@link ISEDAnnotationLink}s.
    */
   public AnnotationAnnotationLinkLabelProvider(ISEDAnnotation annotation) {
      Assert.isNotNull(annotation);
      this.annotation = annotation;
      this.annotation.addAnnotationLinkListener(annotationListener);
      for (ISEDAnnotationLink link : annotation.getLinks()) {
         link.addPropertyChangeListener(linksListener);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getColumnImage(Object element, int columnIndex) {
      if (element instanceof ISEDAnnotationLink) {
         ISEDAnnotationLink link = (ISEDAnnotationLink)element;
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
      if (element instanceof ISEDAnnotationLink) {
         ISEDAnnotationLink link = (ISEDAnnotationLink)element;
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
   protected void handleAnnotationLinkAdded(SEDAnnotationLinkEvent e) {
      e.getLink().addPropertyChangeListener(linksListener);
   }

   /**
    * When an existing annotation link is removed.
    * @param e The event.
    */
   protected void handleAnnotationLinkRemoved(SEDAnnotationLinkEvent e) {
      e.getLink().removePropertyChangeListener(linksListener);
   }

   /**
    * When an {@link ISEDAnnotationLink} has changed.
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
      for (ISEDAnnotationLink link : annotation.getLinks()) {
         link.removePropertyChangeListener(linksListener);
      }
      if (debugModelPresentation != null) {
         debugModelPresentation.dispose();
      }
   }
}
