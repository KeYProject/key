package org.key_project.sed.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.event.ISEAnnotationLinkListener;
import org.key_project.sed.core.model.event.SEAnnotationLinkEvent;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.eclipse.swt.viewer.AbstractLabelProvider;
import org.key_project.util.java.ObjectUtil;

/**
 * An {@link ITableLabelProvider} which shows the registered 
 * {@link ISEAnnotationLink}s of an {@link ISENode}. 
 * @author Martin Hentschel
 */
public class AnnotationLinkLabelProvider extends AbstractLabelProvider implements ITableLabelProvider {
   /**
    * The observed {@link ISENode}.
    */
   private final ISENode node;
   
   /**
    * Listens for changes on {@link #node}.
    */
   private final ISEAnnotationLinkListener nodeListener = new ISEAnnotationLinkListener() {
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
    * Listens for changes on {@link ISEAnnotationLink}s.
    */
   private final PropertyChangeListener annotationLinkListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handlePropertyChange(evt);
      }
   };
   
   /**
    * Constructor.
    * @param node The {@link ISENode} which provides the {@link ISEAnnotationLink}s to observe.
    */
   public AnnotationLinkLabelProvider(ISENode node) {
      this.node = node;
      if (node != null) {
         ISEAnnotationLink[] links = node.getAnnotationLinks();
         for (ISEAnnotationLink link : links) {
            link.addPropertyChangeListener(annotationLinkListener);
         }
         node.addAnnotationLinkListener(nodeListener);
      }
   }

   /**
    * When a new annotation link is added.
    * @param e The event.
    */
   protected void handleAnnotationLinkAdded(SEAnnotationLinkEvent e) {
      e.getLink().addPropertyChangeListener(annotationLinkListener);
   }

   /**
    * When an existing annotation link is removed.
    * @param e The event.
    */
   protected void handleAnnotationLinkRemoved(SEAnnotationLinkEvent e) {
      e.getLink().removePropertyChangeListener(annotationLinkListener);
   }

   /**
    * When a property of an {@link ISEAnnotation} has changed.
    * @param evt The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent evt) {
      if (!ISEAnnotationLink.PROP_SOURCE.equals(evt.getPropertyName()) &&
          !ISEAnnotationLink.PROP_TARGET.equals(evt.getPropertyName())) {
         fireLabelProviderChangedThreadSave(new LabelProviderChangedEvent(this, evt.getSource()));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getColumnText(Object element, int columnIndex) {
      return ObjectUtil.toString(element);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getColumnImage(Object element, int columnIndex) {
      if (columnIndex == 0) {
         if (element instanceof ISEAnnotationLink) {
            return SEDUIUtil.getAnnotationTypeImage(((ISEAnnotationLink) element).getSource().getType());
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
   public void dispose() {
      super.dispose();
      if (node != null) {
         ISEAnnotationLink[] links = node.getAnnotationLinks();
         for (ISEAnnotationLink link : links) {
            link.removePropertyChangeListener(annotationLinkListener);
         }
         node.removeAnnotationLinkListener(nodeListener);
      }
   }
}
