package org.key_project.sed.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.event.ISEDAnnotationListener;
import org.key_project.sed.core.model.event.SEDAnnotationEvent;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.eclipse.swt.viewer.AbstractLabelProvider;
import org.key_project.util.java.ObjectUtil;

/**
 * An {@link ITableLabelProvider} which shows the registered 
 * {@link ISEDAnnotation}s of an {@link ISEDDebugTarget}. 
 * @author Martin Hentschel
 */
public class AnnotationLabelProvider extends AbstractLabelProvider implements ITableLabelProvider {
   /**
    * The observed {@link ISEDDebugTarget}.
    */
   private final ISEDDebugTarget target;
   
   /**
    * Listens for changes on {@link #target}.
    */
   private final ISEDAnnotationListener targetListener = new ISEDAnnotationListener() {
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
      }
   };
   
   /**
    * Listens for changes on {@link ISEDAnnotation}s.
    */
   private final PropertyChangeListener annotationListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handlePropertyChange(evt);
      }
   };
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} which provides the {@link ISEDAnnotation} to observe.
    */
   public AnnotationLabelProvider(ISEDDebugTarget target) {
      this.target = target;
      if (target != null) {
         ISEDAnnotation[] annotations = target.getRegisteredAnnotations();
         for (ISEDAnnotation annotation : annotations) {
            annotation.addPropertyChangeListener(annotationListener);
         }
         target.addAnnotationListener(targetListener);
      }
   }

   /**
    * When a new annotation is registered.
    * @param e The event.
    */
   protected void handleAnnotationRegistered(SEDAnnotationEvent e) {
      e.getAnnotation().addPropertyChangeListener(annotationListener);
   }

   /**
    * When an existing annotation is unregistered.
    * @param e The event.
    */
   protected void handleAnnotationUnregistered(SEDAnnotationEvent e) {
      e.getAnnotation().removePropertyChangeListener(annotationListener);
   }

   /**
    * When a property of an {@link ISEDAnnotation} has changed.
    * @param evt The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent evt) {
      if (!ISEDAnnotation.PROP_ENABLED.equals(evt.getPropertyName()) &&
          !ISEDAnnotation.PROP_TYPE.equals(evt.getPropertyName()) &&
          !ISEDAnnotation.PROP_HIGHLIGHT_BACKGROUND.equals(evt.getPropertyName()) &&
          !ISEDAnnotation.PROP_BACKGROUND_COLOR.equals(evt.getPropertyName()) &&
          !ISEDAnnotation.PROP_HIGHLIGHT_FOREGROUND.equals(evt.getPropertyName()) &&
          !ISEDAnnotation.PROP_FOREGROUND_COLOR.equals(evt.getPropertyName())) {
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
         if (element instanceof ISEDAnnotation) {
            return SEDUIUtil.getAnnotationTypeImage(((ISEDAnnotation) element).getType());
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
      if (target != null) {
         ISEDAnnotation[] annotations = target.getRegisteredAnnotations();
         for (ISEDAnnotation annotation : annotations) {
            annotation.removePropertyChangeListener(annotationListener);
         }
         target.removeAnnotationListener(targetListener);
      }
   }
}
