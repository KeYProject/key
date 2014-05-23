package org.key_project.sed.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.event.ISEDAnnotationLinkListener;
import org.key_project.sed.core.model.event.SEDAnnotationLinkEvent;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.eclipse.swt.viewer.AbstractLabelProvider;
import org.key_project.util.java.ObjectUtil;

/**
 * An {@link ITableLabelProvider} which shows the registered 
 * {@link ISEDAnnotationLink}s of an {@link ISEDDebugNode}. 
 * @author Martin Hentschel
 */
public class AnnotationLinkLabelProvider extends AbstractLabelProvider implements ITableLabelProvider {
   /**
    * The observed {@link ISEDDebugNode}.
    */
   private final ISEDDebugNode node;
   
   /**
    * Listens for changes on {@link #node}.
    */
   private final ISEDAnnotationLinkListener nodeListener = new ISEDAnnotationLinkListener() {
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
    * Listens for changes on {@link ISEDAnnotationLink}s.
    */
   private final PropertyChangeListener annotationLinkListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handlePropertyChange(evt);
      }
   };
   
   /**
    * Constructor.
    * @param node The {@link ISEDDebugNode} which provides the {@link ISEDAnnotationLink}s to observe.
    */
   public AnnotationLinkLabelProvider(ISEDDebugNode node) {
      this.node = node;
      if (node != null) {
         ISEDAnnotationLink[] links = node.getAnnotationLinks();
         for (ISEDAnnotationLink link : links) {
            link.addPropertyChangeListener(annotationLinkListener);
         }
         node.addAnnotationLinkListener(nodeListener);
      }
   }

   /**
    * When a new annotation link is added.
    * @param e The event.
    */
   protected void handleAnnotationLinkAdded(SEDAnnotationLinkEvent e) {
      e.getLink().addPropertyChangeListener(annotationLinkListener);
   }

   /**
    * When an existing annotation link is removed.
    * @param e The event.
    */
   protected void handleAnnotationLinkRemoved(SEDAnnotationLinkEvent e) {
      e.getLink().removePropertyChangeListener(annotationLinkListener);
   }

   /**
    * When a property of an {@link ISEDAnnotation} has changed.
    * @param evt The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent evt) {
      if (!ISEDAnnotationLink.PROP_SOURCE.equals(evt.getPropertyName()) &&
          !ISEDAnnotationLink.PROP_TARGET.equals(evt.getPropertyName())) {
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
         if (element instanceof ISEDAnnotationLink) {
            return SEDUIUtil.getAnnotationTypeImage(((ISEDAnnotationLink) element).getSource().getType());
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
         ISEDAnnotationLink[] links = node.getAnnotationLinks();
         for (ISEDAnnotationLink link : links) {
            link.removePropertyChangeListener(annotationLinkListener);
         }
         node.removeAnnotationLinkListener(nodeListener);
      }
   }
}
