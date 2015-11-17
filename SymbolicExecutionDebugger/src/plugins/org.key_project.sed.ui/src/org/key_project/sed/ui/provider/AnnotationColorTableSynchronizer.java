package org.key_project.sed.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Widget;
import org.eclipse.ui.services.IDisposable;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.event.ISEAnnotationListener;
import org.key_project.sed.core.model.event.SEAnnotationEvent;
import org.key_project.sed.core.util.SEDPreferenceUtil;

/**
 * Shows the colors defined by {@link ISEAnnotation} in an {@link TableViewer}.
 * @author Martin Hentschel
 */
public class AnnotationColorTableSynchronizer implements IDisposable {
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
    * Listens for changes on {@link SEDPreferenceUtil#getStore()}.
    */
   private final IPropertyChangeListener storeListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(org.eclipse.jface.util.PropertyChangeEvent event) {
         handleStorePropertyChange(event);
      }
   };
   
   /**
    * The {@link TableViewer} to show colors in.
    */
   private final TableViewer viewer;
   
   /**
    * Maps an {@link RGB} to the used {@link Color}.
    */
   private final Map<RGB, Color> colorMap = new HashMap<RGB, Color>();

   /**
    * Constructor.
    * @param model The {@link ISEDebugTarget} which provides the {@link ISEAnnotation}s.
    * @param viewer The {@link TableViewer} to show colors in.
    */
   public AnnotationColorTableSynchronizer(ISEDebugTarget model, TableViewer viewer) {
      Assert.isNotNull(model);
      Assert.isNotNull(viewer);
      this.model = model;
      this.model.addAnnotationListener(modelListener);
      SEDPreferenceUtil.getStore().addPropertyChangeListener(storeListener);
      for (ISEAnnotation annotation : model.getRegisteredAnnotations()) {
         addListener(annotation);
      }
      this.viewer = viewer;
      for (TableItem item : viewer.getTable().getItems()) {
         updateColor(item);
      }
   }

   /**
    * When a new {@link ISEAnnotation} is registered.
    * @param e The event.
    */
   protected void handleAnnotationRegistered(SEAnnotationEvent e) {
      addListener(e.getAnnotation());
      updateColor(e.getAnnotation());
   }
   
   /**
    * Adds all required listener to the {@link ISEAnnotation}.
    * @param annotation The {@link ISEAnnotation} to observe.
    */
   protected void addListener(ISEAnnotation annotation) {
      annotation.addPropertyChangeListener(ISEAnnotation.PROP_HIGHLIGHT_BACKGROUND, annotationListener);
      annotation.addPropertyChangeListener(ISEAnnotation.PROP_BACKGROUND_COLOR, annotationListener);
      annotation.addPropertyChangeListener(ISEAnnotation.PROP_HIGHLIGHT_FOREGROUND, annotationListener);
      annotation.addPropertyChangeListener(ISEAnnotation.PROP_FOREGROUND_COLOR, annotationListener);
   }

   /**
    * When an existing {@link ISEAnnotation} was unregistered.
    * @param e The event.
    */
   protected void handleAnnotationUnregistered(SEAnnotationEvent e) {
      removeListener(e.getAnnotation());
   }
   
   /**
    * Removes all listener from the {@link ISEAnnotation}.
    * @param annotation The {@link ISEAnnotation} to remove listener from.
    */
   protected void removeListener(ISEAnnotation annotation) {
      annotation.removePropertyChangeListener(ISEAnnotation.PROP_HIGHLIGHT_BACKGROUND, annotationListener);
      annotation.removePropertyChangeListener(ISEAnnotation.PROP_BACKGROUND_COLOR, annotationListener);
      annotation.removePropertyChangeListener(ISEAnnotation.PROP_HIGHLIGHT_FOREGROUND, annotationListener);
      annotation.removePropertyChangeListener(ISEAnnotation.PROP_FOREGROUND_COLOR, annotationListener);
   }

   /**
    * When {@link ISEAnnotation#isEnabled()} has changed.
    * @param evt The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent evt) {
      updateColor(evt.getSource());
   }

   /**
    * Handles a change on {@link SEDPreferenceUtil#getStore()}.
    * @param event The event.
    */
   protected void handleStorePropertyChange(org.eclipse.jface.util.PropertyChangeEvent event) {
      if (event.getProperty().startsWith(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_HIGHLIGHT_BACKGROUND_PREFIX) ||
          event.getProperty().startsWith(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_BACKGROUND_COLOR_PREFIX) ||
          event.getProperty().startsWith(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_HIGHLIGHT_FOREGROUND_PREFIX) ||
          event.getProperty().startsWith(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_FOREGROUND_COLOR_PREFIX)) {
         for (TableItem item : viewer.getTable().getItems()) {
            updateColor(item);
         }
      }
   }
   
   /**
    * Updates the {@link Color} of the given data object.
    * @param obj The data object.
    */
   protected void updateColor(final Object obj) {
      viewer.getControl().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            Widget item = viewer.testFindItem(obj);
            if (item instanceof TableItem) {
               updateColor((TableItem)item);
            }
         }
      });
   }

   /**
    * Updates the {@link Color}s of the given {@link TableItem}.
    * @param item The {@link TableItem} to update its colors.
    */
   protected void updateColor(TableItem item) {
      if (item.getData() instanceof ISEAnnotation) {
         ISEAnnotation annotation = (ISEAnnotation)item.getData();
         if (annotation.isHighlightBackground()) {
            item.setBackground(createColor(annotation.getBackgroundColor(), item.getDisplay()));
         }
         else {
            item.setBackground(null);
         }
         if (annotation.isHighlightForeground()) {
            item.setForeground(createColor(annotation.getForegroundColor(), item.getDisplay()));
         }
         else {
            item.setForeground(null);
         }
      }
   }
   
   /**
    * Returns the {@link Color} instance for the given {@link RGB} value.
    * @param rgb The {@link RGB} value.
    * @param display The {@link Display} in which the {@link Color} will be used.
    * @return The {@link Color} with the specified {@link RGB}.
    */
   protected Color createColor(RGB rgb, Display display) {
      Color color = colorMap.get(rgb);
      if (color == null) {
         color = new Color(display, rgb);
         colorMap.put(rgb, color);
      }
      return color;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      SEDPreferenceUtil.getStore().removePropertyChangeListener(storeListener);
      model.removeAnnotationListener(modelListener);
      for (ISEAnnotation annotation : model.getRegisteredAnnotations()) {
         removeListener(annotation);
      }
      for (Color color : colorMap.values()) {
         color.dispose();
      }
      colorMap.clear();
   }
}
