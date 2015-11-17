package org.key_project.sed.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.event.ISEAnnotationListener;
import org.key_project.sed.core.model.event.SEAnnotationEvent;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.eclipse.swt.viewer.AbstractLabelProvider;
import org.key_project.util.java.ObjectUtil;

/**
 * An {@link ITableLabelProvider} which shows the registered 
 * {@link ISEAnnotation}s of an {@link ISEDebugTarget}. 
 * @author Martin Hentschel
 */
public class AnnotationLabelProvider extends AbstractLabelProvider implements ITableLabelProvider {
   /**
    * The observed {@link ISEDebugTarget}.
    */
   private final ISEDebugTarget target;
   
   /**
    * Listens for changes on {@link #target}.
    */
   private final ISEAnnotationListener targetListener = new ISEAnnotationListener() {
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
      }
   };
   
   /**
    * Listens for changes on {@link ISEAnnotation}s.
    */
   private final PropertyChangeListener annotationListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handlePropertyChange(evt);
      }
   };
   
   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} which provides the {@link ISEAnnotation} to observe.
    */
   public AnnotationLabelProvider(ISEDebugTarget target) {
      this.target = target;
      if (target != null) {
         ISEAnnotation[] annotations = target.getRegisteredAnnotations();
         for (ISEAnnotation annotation : annotations) {
            annotation.addPropertyChangeListener(annotationListener);
         }
         target.addAnnotationListener(targetListener);
      }
   }

   /**
    * When a new annotation is registered.
    * @param e The event.
    */
   protected void handleAnnotationRegistered(SEAnnotationEvent e) {
      e.getAnnotation().addPropertyChangeListener(annotationListener);
   }

   /**
    * When an existing annotation is unregistered.
    * @param e The event.
    */
   protected void handleAnnotationUnregistered(SEAnnotationEvent e) {
      e.getAnnotation().removePropertyChangeListener(annotationListener);
   }

   /**
    * When a property of an {@link ISEAnnotation} has changed.
    * @param evt The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent evt) {
      if (!ISEAnnotation.PROP_ENABLED.equals(evt.getPropertyName()) &&
          !ISEAnnotation.PROP_TYPE.equals(evt.getPropertyName()) &&
          !ISEAnnotation.PROP_HIGHLIGHT_BACKGROUND.equals(evt.getPropertyName()) &&
          !ISEAnnotation.PROP_BACKGROUND_COLOR.equals(evt.getPropertyName()) &&
          !ISEAnnotation.PROP_HIGHLIGHT_FOREGROUND.equals(evt.getPropertyName()) &&
          !ISEAnnotation.PROP_FOREGROUND_COLOR.equals(evt.getPropertyName())) {
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
         if (element instanceof ISEAnnotation) {
            return SEDUIUtil.getAnnotationTypeImage(((ISEAnnotation) element).getType());
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
         ISEAnnotation[] annotations = target.getRegisteredAnnotations();
         for (ISEAnnotation annotation : annotations) {
            annotation.removePropertyChangeListener(annotationListener);
         }
         target.removeAnnotationListener(targetListener);
      }
   }
}
