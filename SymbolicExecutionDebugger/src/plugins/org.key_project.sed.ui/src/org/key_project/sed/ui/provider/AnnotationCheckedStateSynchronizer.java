package org.key_project.sed.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.ui.services.IDisposable;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.event.ISEAnnotationListener;
import org.key_project.sed.core.model.event.SEAnnotationEvent;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * Synchronizes {@link ISEAnnotation#isEnabled()} with the check boxes
 * of a {@link CheckboxTableViewer}.
 * @author Martin Hentschel
 */
public class AnnotationCheckedStateSynchronizer implements IDisposable {
   /**
    * The model to synchronize with.
    */
   private final ISEDebugTarget model;
   
   /**
    * Observes {@link #modelListener}.
    */
   private final ISEAnnotationListener modelListener = new ISEAnnotationListener() {
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
    * Observes {@link ISEAnnotation}s provided by {@link #model}.
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
   public AnnotationCheckedStateSynchronizer(ISEDebugTarget model, CheckboxTableViewer viewer) {
      Assert.isNotNull(model);
      Assert.isNotNull(viewer);
      this.model = model;
      this.model.addAnnotationListener(modelListener);
      this.viewer = viewer;
      this.viewer.addCheckStateListener(viewerListener);
      for (ISEAnnotation annotation : model.getRegisteredAnnotations()) {
         annotation.addPropertyChangeListener(ISEAnnotation.PROP_ENABLED, annotationListener);
         viewer.setChecked(annotation, annotation.isEnabled());
      }
   }

   /**
    * When a new {@link ISEAnnotation} is registered.
    * @param e The event.
    */
   protected void handleAnnotationRegistered(SEAnnotationEvent e) {
      ISEAnnotation annotation = e.getAnnotation();
      annotation.addPropertyChangeListener(ISEAnnotation.PROP_ENABLED, annotationListener);
      SWTUtil.setChecked(viewer, annotation, annotation.isEnabled());
   }

   /**
    * When an existing {@link ISEAnnotation} was unregistered.
    * @param e The event.
    */
   protected void handleAnnotationUnregistered(SEAnnotationEvent e) {
      e.getAnnotation().removePropertyChangeListener(ISEAnnotation.PROP_ENABLED, annotationListener);
   }

   /**
    * When {@link ISEAnnotation#isEnabled()} has changed.
    * @param evt The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent evt) {
      ISEAnnotation annotation = (ISEAnnotation)evt.getSource();
      SWTUtil.setChecked(viewer, annotation, annotation.isEnabled());
   }

   /**
    * When the checked state has changed in {@link #viewer}.
    * @param event The event.
    */
   protected void handleCheckStateChanged(CheckStateChangedEvent event) {
      if (event.getElement() instanceof ISEAnnotation) {
         ((ISEAnnotation)event.getElement()).setEnabled(event.getChecked());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      this.model.removeAnnotationListener(modelListener);
      for (ISEAnnotation annotation : model.getRegisteredAnnotations()) {
         annotation.removePropertyChangeListener(ISEAnnotation.PROP_ENABLED, annotationListener);
      }
      this.viewer.removeCheckStateListener(viewerListener);
   }
}
