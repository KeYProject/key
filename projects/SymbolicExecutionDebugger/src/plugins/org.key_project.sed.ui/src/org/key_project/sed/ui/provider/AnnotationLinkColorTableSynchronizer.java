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
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.event.ISEDAnnotationLinkListener;
import org.key_project.sed.core.model.event.SEDAnnotationLinkEvent;
import org.key_project.sed.core.util.SEDPreferenceUtil;

/**
 * Shows the colors defined by {@link ISEDAnnotation} in an {@link TableViewer}.
 * @author Martin Hentschel
 */
public class AnnotationLinkColorTableSynchronizer implements IDisposable {
   /**
    * The model to synchronize with.
    */
   private final ISEDDebugNode model;
   
   /**
    * Observes {@link #modelListener}.
    */
   private final ISEDAnnotationLinkListener modelListener = new ISEDAnnotationLinkListener() {
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
    * Observes {@link ISEDAnnotation}s provided by {@link #model}.
    */
   private final PropertyChangeListener annotationListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handlePropertyChange(evt);
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
    * Listens for changes on {@link SEDPreferenceUtil#getStore()}.
    */
   private final IPropertyChangeListener storeListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(org.eclipse.jface.util.PropertyChangeEvent event) {
         handleStorePropertyChange(event);
      }
   };

   /**
    * Constructor.
    * @param model The {@link ISEDDebugTarget} which provides the {@link ISEDAnnotation}s.
    * @param viewer The {@link TableViewer} to show colors in.
    */
   public AnnotationLinkColorTableSynchronizer(ISEDDebugNode model, TableViewer viewer) {
      Assert.isNotNull(model);
      Assert.isNotNull(viewer);
      this.model = model;
      this.model.addAnnotationLinkListener(modelListener);
      SEDPreferenceUtil.getStore().addPropertyChangeListener(storeListener);
      for (ISEDAnnotationLink link : model.getAnnotationLinks()) {
         addListener(link);
      }
      this.viewer = viewer;
      for (TableItem item : viewer.getTable().getItems()) {
         updateColor(item);
      }
   }

   /**
    * When a new {@link ISEDAnnotationLink} is added.
    * @param e The event.
    */
   protected void handleAnnotationLinkAdded(SEDAnnotationLinkEvent e) {
      addListener(e.getLink());
      updateColor(e.getLink());
   }
   
   /**
    * Adds all required listener to the {@link ISEDAnnotationLink}.
    * @param link The {@link ISEDAnnotationLink} to observe.
    */
   protected void addListener(ISEDAnnotationLink link) {
      ISEDAnnotation annotation = link.getSource();
      annotation.addPropertyChangeListener(ISEDAnnotation.PROP_HIGHLIGHT_BACKGROUND, annotationListener);
      annotation.addPropertyChangeListener(ISEDAnnotation.PROP_BACKGROUND_COLOR, annotationListener);
      annotation.addPropertyChangeListener(ISEDAnnotation.PROP_HIGHLIGHT_FOREGROUND, annotationListener);
      annotation.addPropertyChangeListener(ISEDAnnotation.PROP_FOREGROUND_COLOR, annotationListener);
   }

   /**
    * When an existing {@link ISEDAnnotationLink} was removed.
    * @param e The event.
    */
   protected void handleAnnotationLinkRemoved(SEDAnnotationLinkEvent e) {
      removeListener(e.getLink());
   }
   
   /**
    * Removes all listener from the {@link ISEDAnnotationLink}.
    * @param link The {@link ISEDAnnotationLink} to remove listener from.
    */
   protected void removeListener(ISEDAnnotationLink link) {
      ISEDAnnotation annotation = link.getSource();
      annotation.removePropertyChangeListener(ISEDAnnotation.PROP_HIGHLIGHT_BACKGROUND, annotationListener);
      annotation.removePropertyChangeListener(ISEDAnnotation.PROP_BACKGROUND_COLOR, annotationListener);
      annotation.removePropertyChangeListener(ISEDAnnotation.PROP_HIGHLIGHT_FOREGROUND, annotationListener);
      annotation.removePropertyChangeListener(ISEDAnnotation.PROP_FOREGROUND_COLOR, annotationListener);
   }

   /**
    * When {@link ISEDAnnotation#isEnabled()} has changed.
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
      if (item.getData() instanceof ISEDAnnotationLink) {
         ISEDAnnotationLink link = (ISEDAnnotationLink)item.getData();
         ISEDAnnotation annotation = link.getSource();
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
      model.removeAnnotationLinkListener(modelListener);
      for (ISEDAnnotationLink link : model.getAnnotationLinks()) {
         removeListener(link);
      }
      for (Color color : colorMap.values()) {
         color.dispose();
      }
      colorMap.clear();
   }
}
