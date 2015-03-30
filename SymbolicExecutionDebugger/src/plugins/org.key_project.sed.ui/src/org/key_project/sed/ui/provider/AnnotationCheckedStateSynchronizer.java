package org.key_project.sed.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.ui.services.IDisposable;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.event.ISEDAnnotationListener;
import org.key_project.sed.core.model.event.SEDAnnotationEvent;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * Synchronizes {@link ISEDAnnotation#isEnabled()} with the check boxes
 * of a {@link CheckboxTableViewer}.
 * @author Martin Hentschel
 */
public class AnnotationCheckedStateSynchronizer implements IDisposable {
   /**
    * The model to synchronize with.
    */
   private final ISEDDebugTarget model;
   
   /**
    * Observes {@link #modelListener}.
    */
   private final ISEDAnnotationListener modelListener = new ISEDAnnotationListener() {
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
    * Observes {@link ISEDAnnotation}s provided by {@link #model}.
    */
   private final PropertyChangeListener annotationListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handlePropertyChange(evt);
      }
   };
   
   /**
    * The {@link CheckboxTableViewer} to synchronize with.
    */
   private final CheckboxTableViewer viewer;

   /**
    * Observes {@link #viewer}.
    */
   private final ICheckStateListener viewerListener = new ICheckStateListener() {
      @Override
      public void checkStateChanged(CheckStateChangedEvent event) {
         handleCheckStateChanged(event);
      }
   };
   
   /**
    * Constructor.
    * @param model The model to synchronize with.
    * @param viewer The {@link CheckboxTableViewer} to synchronize with.
    */
   public AnnotationCheckedStateSynchronizer(ISEDDebugTarget model, CheckboxTableViewer viewer) {
      Assert.isNotNull(model);
      Assert.isNotNull(viewer);
      this.model = model;
      this.model.addAnnotationListener(modelListener);
      this.viewer = viewer;
      this.viewer.addCheckStateListener(viewerListener);
      for (ISEDAnnotation annotation : model.getRegisteredAnnotations()) {
         annotation.addPropertyChangeListener(ISEDAnnotation.PROP_ENABLED, annotationListener);
         viewer.setChecked(annotation, annotation.isEnabled());
      }
   }

   /**
    * When a new {@link ISEDAnnotation} is registered.
    * @param e The event.
    */
   protected void handleAnnotationRegistered(SEDAnnotationEvent e) {
      ISEDAnnotation annotation = e.getAnnotation();
      annotation.addPropertyChangeListener(ISEDAnnotation.PROP_ENABLED, annotationListener);
      SWTUtil.setChecked(viewer, annotation, annotation.isEnabled());
   }

   /**
    * When an existing {@link ISEDAnnotation} was unregistered.
    * @param e The event.
    */
   protected void handleAnnotationUnregistered(SEDAnnotationEvent e) {
      e.getAnnotation().removePropertyChangeListener(ISEDAnnotation.PROP_ENABLED, annotationListener);
   }

   /**
    * When {@link ISEDAnnotation#isEnabled()} has changed.
    * @param evt The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent evt) {
      ISEDAnnotation annotation = (ISEDAnnotation)evt.getSource();
      SWTUtil.setChecked(viewer, annotation, annotation.isEnabled());
   }

   /**
    * When the checked state has changed in {@link #viewer}.
    * @param event The event.
    */
   protected void handleCheckStateChanged(CheckStateChangedEvent event) {
      if (event.getElement() instanceof ISEDAnnotation) {
         ((ISEDAnnotation)event.getElement()).setEnabled(event.getChecked());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      this.model.removeAnnotationListener(modelListener);
      for (ISEDAnnotation annotation : model.getRegisteredAnnotations()) {
         annotation.removePropertyChangeListener(ISEDAnnotation.PROP_ENABLED, annotationListener);
      }
      this.viewer.removeCheckStateListener(viewerListener);
   }
}
