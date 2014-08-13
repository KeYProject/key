/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.ui.visualization.execution_tree.editor;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.IDebugEventSetListener;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.impl.AdapterImpl;
import org.eclipse.gef.ContextMenuProvider;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.CustomContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.internal.ExternalPictogramLink;
import org.eclipse.graphiti.mm.Property;
import org.eclipse.graphiti.mm.algorithms.styles.Style;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.notification.INotificationService;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.event.ISEDAnnotationLinkListener;
import org.key_project.sed.core.annotation.event.SEDAnnotationLinkEvent;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.event.ISEDAnnotationListener;
import org.key_project.sed.core.model.event.SEDAnnotationEvent;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.sed.ui.visualization.execution_tree.feature.AbstractDebugNodeUpdateFeature;
import org.key_project.sed.ui.visualization.execution_tree.service.SEDNotificationService;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.execution_tree.wizard.SaveAsExecutionTreeDiagramWizard;
import org.key_project.sed.ui.visualization.util.CustomizableDiagramEditorContextMenuProvider;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.sed.ui.visualization.util.PaletteHideableDiagramEditor;
import org.key_project.sed.ui.visualization.util.VisualizationPreferences;
import org.key_project.util.eclipse.job.AbstractDependingOnObjectsJob;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * {@link DiagramEditor} for Symbolic Execution Tree Diagrams.
 * @author Martin Hentschel
 */
// TODO: Reload diagram when the domain model file has changed.
@SuppressWarnings("restriction")
public class ExecutionTreeDiagramEditor extends PaletteHideableDiagramEditor {
   /**
    * Indicates that this editor is read-only or editable otherwise.
    */
   private boolean readOnly;

   /**
    * Listens for debug events.
    */
   private final IDebugEventSetListener debugListener = new IDebugEventSetListener() {
      @Override
      public void handleDebugEvents(DebugEvent[] events) {
         ExecutionTreeDiagramEditor.this.handleDebugEvents(events);
      }
   };

   /**
    * Observes {@link #getDiagram()}.
    */
   private final Adapter diagramListener = new AdapterImpl() {
      @Override
      public void notifyChanged(Notification msg) {
         handleNotifyChanged(msg);
      }
   };
   
   /**
    * All observed {@link ISEDDebugTarget}s.
    */
   private final List<ISEDDebugTarget> observedTargets = new LinkedList<ISEDDebugTarget>();
   
   /**
    * Listens for changes on all shown {@link ISEDDebugTarget}s.
    */
   private final ISEDAnnotationListener targetListener = new ISEDAnnotationListener() {
      @Override
      public void annotationUnregistered(SEDAnnotationEvent e) {
         handleAnnotationUnregistered(e);
      }
      
      @Override
      public void annotationRegistered(SEDAnnotationEvent e) {
         handleAnnotationRegistered(e);
      }
      
      @Override
      public void annotationMoved(SEDAnnotationEvent e) {
         handleAnnotationMoved(e);
      }
   };
   
   /**
    * Listens for changes on {@link ISEDAnnotation}s.
    */
   private final PropertyChangeListener annotationListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleAnnotationPropertyChange(evt);
      }
   };

   /**
    * Listens for changes on {@link ISEDAnnotation}s.
    */
   private final ISEDAnnotationLinkListener annotationLinkListener = new ISEDAnnotationLinkListener() {
      @Override
      public void annotationLinkRemoved(SEDAnnotationLinkEvent e) {
         handleAnnotationLinkRemoved(e);
      }
      
      @Override
      public void annotationLinkAdded(SEDAnnotationLinkEvent e) {
         handleAnnotationLinkAdded(e);
      }
   };

   /**
    * Observes {@link SEDPreferenceUtil#getStore()}.
    */
   private final IPropertyChangeListener sedStorePropertyChangeListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(org.eclipse.jface.util.PropertyChangeEvent event) {
         handleSedStorePropertyChange(event);
      }
   };

   /**
    * Observes {@link VisualizationPreferences#getStore()}.
    */
   private final IPropertyChangeListener visualizationStorePropertyChangeListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(org.eclipse.jface.util.PropertyChangeEvent event) {
         handleVisualizationStorePropertyChange(event);
      }
   };
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isSaveAsAllowed() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void doSaveAs() {
      SaveAsExecutionTreeDiagramWizard.openWizard(getSite().getShell(), getDiagramTypeProvider());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void registerBOListener() {
      super.registerBOListener();
      getDiagram().eAdapters().add(diagramListener);
      DebugPlugin.getDefault().addDebugEventListener(debugListener);
      SEDPreferenceUtil.getStore().addPropertyChangeListener(sedStorePropertyChangeListener);
      VisualizationPreferences.getStore().addPropertyChangeListener(visualizationStorePropertyChangeListener);
   }

   /**
    * When something on {@link #getDiagram()} has changed.
    * @param msg The event.
    */
   protected void handleNotifyChanged(Notification msg) {
      if (msg.getNewValue() instanceof Property) {
         Property property = (Property)msg.getNewValue();
         if (ExternalPictogramLink.KEY_INDEPENDENT_PROPERTY.equals(property.getKey())) {
            for (ISEDDebugTarget target : observedTargets) {
               unobserveDebugTarget(target);
            }
            observedTargets.clear();
            Object[] bos = getDiagramTypeProvider().getFeatureProvider().getAllBusinessObjectsForPictogramElement(getDiagram());
            for (Object bo : bos) {
               if (bo instanceof ISEDDebugTarget) {
                  ISEDDebugTarget target = (ISEDDebugTarget)bo;
                  observeDebugTarget(target);
                  observedTargets.add(target);
               }
            }
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void unregisterBOListener() {
      super.unregisterBOListener();
      getDiagram().eAdapters().remove(diagramListener);
      DebugPlugin.getDefault().removeDebugEventListener(debugListener);
      SEDPreferenceUtil.getStore().removePropertyChangeListener(sedStorePropertyChangeListener );
      VisualizationPreferences.getStore().removePropertyChangeListener(visualizationStorePropertyChangeListener);
   }

   /**
    * Handles the detected debug events. 
    * @param events The detected debug events.
    */
   protected void handleDebugEvents(DebugEvent[] events) {
      // Check if an update of the diagram is required.
      ISEDDebugTarget[] targets = ExecutionTreeUtil.getAllDebugTargets(getDiagramTypeProvider());
      boolean updateRequired = false;
      int i = 0;
      while (!updateRequired && i < events.length) {
         if (DebugEvent.SUSPEND == events[i].getKind() ||
             DebugEvent.SUSPEND == events[i].getKind()) {
            if (events[i].getSource() instanceof IDebugElement) {
               IDebugTarget target = ((IDebugElement)events[i].getSource()).getDebugTarget();
               if (target instanceof ISEDDebugTarget) {
                  updateRequired = ArrayUtil.contains(targets, target);
               }
            }
         }
         i++;
      }
      // Update diagram content if required.
      if (updateRequired) {
         // Do an asynchronous update in the UI thread (same behavior as DomainModelChangeListener which is responsible for changes in EMF objects)
         AbstractDependingOnObjectsJob.cancelJobs(this);
         new AbstractDependingOnObjectsJob("Updating Symbolic Execution Tree", this, PlatformUI.getWorkbench()) {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
               return updateDiagramInJob(monitor);
            }
         }.schedule();
      }
   }
   
   /**
    * Changes the content of the shown {@link Diagram}.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The result {@link IStatus}.
    */
   protected IStatus updateDiagramInJob(IProgressMonitor monitor) {
      try {
         SWTUtil.checkCanceled(monitor);
         if (getDiagramTypeProvider().isAutoUpdateAtRuntime()) {
            PictogramElement[] oldSelection = getSelectedPictogramElements();
            PictogramElement[] elements = GraphitiUtil.getAllPictogramElements(getDiagram());
            INotificationService notificationService = getDiagramTypeProvider().getNotificationService();
            if (notificationService instanceof SEDNotificationService) {
               ((SEDNotificationService)notificationService).updatePictogramElements(elements, monitor);
            }
            else {
               notificationService.updatePictogramElements(elements);
            }
            selectPictogramElementsThreadSave(oldSelection);
         }
         else {
            refreshContent();
         }
         return Status.OK_STATUS;
      }
      catch (OperationCanceledException e) {
         return Status.CANCEL_STATUS;
      }
      catch (Exception e) {
         return LogUtil.getLogger().createErrorStatus(e);
      }
   }
   
   /**
    * Thread and exception save execution of {@link #selectPictogramElements(PictogramElement[])}.
    * @param pictogramElements The {@link PictogramElement}s to select.
    */
   protected void selectPictogramElementsThreadSave(final PictogramElement[] pictogramElements) {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            try {
               selectPictogramElements(pictogramElements);
            }
            catch (Exception e) {
               // Can go wrong, nothing to do.
            }
         }
      });
   }

   /**
    * Returns the shown {@link Diagram}.
    * @return The shown {@link Diagram}.
    */
   protected Diagram getDiagram() {
      IDiagramTypeProvider typeProvider = getDiagramTypeProvider();
      return typeProvider != null ? typeProvider.getDiagram() : null;
   }
   
   /**
    * Checks if this editor is read-only or editable.
    * @return {@code true} read-only, {@code false} editable
    */
   public boolean isReadOnly() {
      return readOnly;
   }

   /**
    * Defines if this editor is read-only or editable.
    * @param readOnly {@code true} read-only, {@code false} editable
    */
   public void setReadOnly(boolean readOnly) {
      this.readOnly = readOnly;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDirty() {
      return !isReadOnly() && super.isDirty();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ContextMenuProvider createContextMenuProvider() {
      return new CustomizableDiagramEditorContextMenuProvider(getGraphicalViewer(), 
                                                              getActionRegistry(), 
                                                              getConfigurationProvider(),
                                                              !isReadOnly(),
                                                              !isReadOnly());
   }

   /**
    * Registers listeners on the given {@link ISEDDebugTarget}.
    * @param target The {@link ISEDDebugTarget} to observe.
    */
   protected void observeDebugTarget(ISEDDebugTarget target) {
      if (target != null) {
         target.addAnnotationListener(targetListener);
         ISEDAnnotation[] annotations = target.getRegisteredAnnotations();
         for (ISEDAnnotation annotation : annotations) {
            observeAnnotation(annotation);
         }
      }
   }

   /**
    * Removes all listeners from the given {@link ISEDDebugTarget}.
    * @param target The {@link ISEDDebugTarget} to unobersve.
    */
   protected void unobserveDebugTarget(ISEDDebugTarget target) {
      if (target != null) {
         target.removeAnnotationListener(targetListener);
         ISEDAnnotation[] annotations = target.getRegisteredAnnotations();
         for (ISEDAnnotation annotation : annotations) {
            unobserveAnnotation(annotation);
         }
      }
   }
   
   /**
    * Registers listeners on the given {@link ISEDAnnotation}.
    * @param target The {@link ISEDAnnotation} to observe.
    */
   protected void observeAnnotation(ISEDAnnotation annotation) {
      annotation.addPropertyChangeListener(ISEDAnnotation.PROP_ENABLED, annotationListener);
      annotation.addPropertyChangeListener(ISEDAnnotation.PROP_HIGHLIGHT_BACKGROUND, annotationListener);
      annotation.addPropertyChangeListener(ISEDAnnotation.PROP_BACKGROUND_COLOR, annotationListener);
      annotation.addPropertyChangeListener(ISEDAnnotation.PROP_HIGHLIGHT_FOREGROUND, annotationListener);
      annotation.addPropertyChangeListener(ISEDAnnotation.PROP_FOREGROUND_COLOR, annotationListener);
      annotation.addAnnotationLinkListener(annotationLinkListener);
   }
   
   /**
    * Removes all listeners from the given {@link ISEDAnnotation}.
    * @param target The {@link ISEDAnnotation} to unobersve.
    */
   protected void unobserveAnnotation(ISEDAnnotation annotation) {
      annotation.removePropertyChangeListener(ISEDAnnotation.PROP_ENABLED, annotationListener);
      annotation.removePropertyChangeListener(ISEDAnnotation.PROP_HIGHLIGHT_BACKGROUND, annotationListener);
      annotation.removePropertyChangeListener(ISEDAnnotation.PROP_BACKGROUND_COLOR, annotationListener);
      annotation.removePropertyChangeListener(ISEDAnnotation.PROP_HIGHLIGHT_FOREGROUND, annotationListener);
      annotation.removePropertyChangeListener(ISEDAnnotation.PROP_FOREGROUND_COLOR, annotationListener);
      annotation.removeAnnotationLinkListener(annotationLinkListener );
   }

   /**
    * When a new {@link ISEDAnnotation} was added to an {@link ISEDDebugTarget}.
    * @param e The event.
    */
   protected void handleAnnotationRegistered(SEDAnnotationEvent e) {
      ISEDAnnotation annotation = e.getAnnotation();
      observeAnnotation(annotation);
      if (annotation.isEnabled()) {
         updateStyle(annotation.listLinkTargets());
      }
   }

   /**
    * When an existing {@link ISEDAnnotation} was removed from an {@link ISEDDebugTarget}.
    * @param e The event.
    */
   protected void handleAnnotationUnregistered(SEDAnnotationEvent e) {
      ISEDAnnotation annotation = e.getAnnotation();
      unobserveAnnotation(annotation);
      if (annotation.isEnabled()) {
         updateStyle(annotation.listLinkTargets());
      }
   }

   /**
    * When an {@link ISEDAnnotation} has moved on an {@link ISEDDebugTarget}.
    * @param e The event.
    */
   protected void handleAnnotationMoved(SEDAnnotationEvent e) {
      ISEDAnnotation annotation = e.getAnnotation();
      if (annotation.isEnabled()) {
         updateStyle(annotation.listLinkTargets());
      }
   }

   /**
    * When a property of an {@link ISEDAnnotation} has changed.
    * @param evt The event.
    */
   protected void handleAnnotationPropertyChange(PropertyChangeEvent evt) {
      ISEDAnnotation annotation = (ISEDAnnotation)evt.getSource();
      if (ISEDAnnotation.PROP_ENABLED.equals(evt.getPropertyName())) {
         updateStyle(annotation.listLinkTargets());
      }
      else {
         if (annotation.isEnabled()) {
            updateStyle(annotation.listLinkTargets());
         }
      }
   }

   /**
    * When an {@link ISEDAnnotationLink} was added to an {@link ISEDAnnotation}.
    * @param e The event.
    */
   protected void handleAnnotationLinkAdded(SEDAnnotationLinkEvent e) {
      if (e.getLink().getSource().isEnabled()) {
         updateStyle(Collections.singleton(e.getLink().getTarget()));
      }
   }

   /**
    * When an {@link ISEDAnnotationLink} was removed from an {@link ISEDAnnotation}.
    * @param e The event.
    */
   protected void handleAnnotationLinkRemoved(SEDAnnotationLinkEvent e) {
      if (e.getLink().getSource().isEnabled()) {
         updateStyle(Collections.singleton(e.getLink().getTarget()));
      }
   }

   /**
    * When something has changed on {@link SEDPreferenceUtil#getStore()}.
    * @param event The event.
    */
   protected void handleSedStorePropertyChange(org.eclipse.jface.util.PropertyChangeEvent event) {
      if (event.getProperty().startsWith(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_HIGHLIGHT_BACKGROUND_PREFIX) ||
          event.getProperty().startsWith(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_BACKGROUND_COLOR_PREFIX) ||
          event.getProperty().startsWith(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_HIGHLIGHT_FOREGROUND_PREFIX) ||
          event.getProperty().startsWith(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_FOREGROUND_COLOR_PREFIX)) {
         Set<ISEDDebugNode> nodes = new HashSet<ISEDDebugNode>();
         for (ISEDDebugTarget target : observedTargets) {
            ISEDAnnotation[] annotations = target.getRegisteredAnnotations();
            for (ISEDAnnotation annotation : annotations) {
               nodes.addAll(annotation.listLinkTargets());
            }
         }
         updateStyle(nodes);
      }
   }

   /**
    * When something has changed on {@link VisualizationPreferences#getStore()}.
    * @param event The event.
    */
   protected void handleVisualizationStorePropertyChange(org.eclipse.jface.util.PropertyChangeEvent event) {
      ICustomFeature feature = null;
      if (VisualizationPreferences.EXECUTION_TREE_NODE_FIRST_BACKGROUND_COLOR.equals(event.getProperty()) ||
          VisualizationPreferences.EXECUTION_TREE_NODE_SECOND_BACKGROUND_COLOR.equals(event.getProperty()) ||
          VisualizationPreferences.EXECUTION_TREE_NODE_BACKGROUND_DIRECTION.equals(event.getProperty()) ||
          VisualizationPreferences.EXECUTION_TREE_NODE_FOREGROUND_COLOR.equals(event.getProperty())) {
         final Diagram diagram = getDiagram();
         feature = new AbstractCustomFeature(getDiagramTypeProvider().getFeatureProvider()) {
            @Override
            public boolean canExecute(ICustomContext context) {
               return true;
            }
            
            @Override
            public void execute(ICustomContext context) {
               ExecutionTreeStyleUtil.getStyleForDebugNode(new ISEDAnnotation[0], diagram);
               ExecutionTreeStyleUtil.getStyleForDebugNodeText(new ISEDAnnotation[0], diagram);
            }
         };
      }
      else if (VisualizationPreferences.EXECUTION_TREE_NODE_TEXT_COLOR.equals(event.getProperty())) {
         final Diagram diagram = getDiagram();
         feature = new AbstractCustomFeature(getDiagramTypeProvider().getFeatureProvider()) {
            @Override
            public boolean canExecute(ICustomContext context) {
               return true;
            }
            
            @Override
            public void execute(ICustomContext context) {
               ExecutionTreeStyleUtil.getStyleForDebugNodeText(new ISEDAnnotation[0], diagram);
            }
         };
      }
      else if (VisualizationPreferences.EXECUTION_TREE_NODE_CONNECTION_COLOR.equals(event.getProperty())) {
         final Diagram diagram = getDiagram();
         feature = new AbstractCustomFeature(getDiagramTypeProvider().getFeatureProvider()) {
            @Override
            public boolean canExecute(ICustomContext context) {
               return true;
            }
            
            @Override
            public void execute(ICustomContext context) {
               ExecutionTreeStyleUtil.getStyleForParentConnection(diagram);
            }
         };
      }
      if (feature != null) {
         // Update style
         executeFeature(feature, new CustomContext());
         // Refersh UI
         if (!getSite().getShell().isDisposed()) {
            getSite().getShell().getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  refresh();
               }
            });
         }
      }
   }
   
   /**
    * Updates the {@link Style}s of all {@link PictogramElement}s
    * representing one of the given {@link ISEDDebugNode}s.
    * @param nodes The {@link ISEDDebugNode}s to update the {@link Style}s of their {@link PictogramElement}s.
    */
   protected void updateStyle(Set<ISEDDebugNode> nodes) {
      if (!nodes.isEmpty()) {
         boolean refreshRequired = false;
         IFeatureProvider fp = getDiagramTypeProvider().getFeatureProvider();
         for (ISEDDebugNode node : nodes) {
            PictogramElement[] pes = fp.getAllPictogramElementsForBusinessObject(node);
            if (!refreshRequired && pes.length >= 1) {
               refreshRequired = true;
            }
            for (PictogramElement pe : pes) {
               UpdateContext updateContext = new UpdateContext(pe);
               updateContext.putProperty(AbstractDebugNodeUpdateFeature.KEY_UPDATE_STYLE, Boolean.TRUE);
               updateContext.putProperty(AbstractDebugNodeUpdateFeature.KEY_SED_NODE, node);
               fp.updateIfPossibleAndNeeded(updateContext);
            }
         }
         if (refreshRequired && !getSite().getShell().isDisposed()) {
            getSite().getShell().getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  refresh();
               }
            });
         }
      }
   }
}