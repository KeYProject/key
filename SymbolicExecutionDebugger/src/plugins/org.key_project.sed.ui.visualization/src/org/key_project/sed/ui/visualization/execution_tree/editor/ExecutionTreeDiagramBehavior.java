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
import org.eclipse.gef.ui.palette.FlyoutPaletteComposite;
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
import org.eclipse.graphiti.ui.editor.DefaultPaletteBehavior;
import org.eclipse.graphiti.ui.editor.DefaultPersistencyBehavior;
import org.eclipse.graphiti.ui.editor.DiagramBehavior;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.event.ISEAnnotationLinkListener;
import org.key_project.sed.core.annotation.event.SEAnnotationLinkEvent;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.event.ISEAnnotationListener;
import org.key_project.sed.core.model.event.SEAnnotationEvent;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.sed.ui.visualization.execution_tree.feature.AbstractDebugNodeUpdateFeature;
import org.key_project.sed.ui.visualization.execution_tree.service.SENotificationService;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.CustomizableDiagramEditorContextMenuProvider;
import org.key_project.sed.ui.visualization.util.EmptyDiagramPersistencyBehavior;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.sed.ui.visualization.util.VisualizationPreferences;
import org.key_project.util.eclipse.job.AbstractDependingOnObjectsJob;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * The {@link DiagramBehavior} of an {@link ExecutionTreeDiagramEditor}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class ExecutionTreeDiagramBehavior extends DiagramBehavior {
   /**
    * The {@link ExecutionTreeDiagramEditor} in which this {@link DiagramBehavior} is used.
    */
   private ExecutionTreeDiagramEditor diagramEditor;
   
   /**
    * Indicates that this editor is read-only or editable otherwise.
    */
   private boolean readOnly;

   /**
    * Listens for debug events.
    */
   private IDebugEventSetListener debugListener = new IDebugEventSetListener() {
      @Override
      public void handleDebugEvents(DebugEvent[] events) {
         ExecutionTreeDiagramBehavior.this.handleDebugEvents(events);
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
    * All observed {@link ISEDebugTarget}s.
    */
   private final List<ISEDebugTarget> observedTargets = new LinkedList<ISEDebugTarget>();
   
   /**
    * Listens for changes on all shown {@link ISEDebugTarget}s.
    */
   private final ISEAnnotationListener targetListener = new ISEAnnotationListener() {
      @Override
      public void annotationUnregistered(SEAnnotationEvent e) {
         handleAnnotationUnregistered(e);
      }
      
      @Override
      public void annotationRegistered(SEAnnotationEvent e) {
         handleAnnotationRegistered(e);
      }
      
      @Override
      public void annotationMoved(SEAnnotationEvent e) {
         handleAnnotationMoved(e);
      }
   };
   
   /**
    * Listens for changes on {@link ISEAnnotation}s.
    */
   private final PropertyChangeListener annotationListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleAnnotationPropertyChange(evt);
      }
   };

   /**
    * Listens for changes on {@link ISEAnnotation}s.
    */
   private final ISEAnnotationLinkListener annotationLinkListener = new ISEAnnotationLinkListener() {
      @Override
      public void annotationLinkRemoved(SEAnnotationLinkEvent e) {
         handleAnnotationLinkRemoved(e);
      }
      
      @Override
      public void annotationLinkAdded(SEAnnotationLinkEvent e) {
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
    * Constructor.
    * @param diagramEditor The {@link ExecutionTreeDiagramEditor} in which this {@link DiagramBehavior} is used.
    * @param readOnly Indicates that this behavior is read-only or editable otherwise.
    */
   public ExecutionTreeDiagramBehavior(ExecutionTreeDiagramEditor diagramEditor, boolean readOnly) {
      super(diagramEditor);
      this.diagramEditor = diagramEditor;
      this.readOnly = readOnly;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected DefaultPaletteBehavior createPaletteBehaviour() {
      DefaultPaletteBehavior paletteBehaviour = super.createPaletteBehaviour();
      paletteBehaviour.getPalettePreferences().setPaletteState(FlyoutPaletteComposite.STATE_PINNED_OPEN); // Make sure that palette is visible, it is later hidden via ExecutionTreeToolBehaviorProvider#isShowFlyoutPalette()
      return paletteBehaviour;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected DefaultPersistencyBehavior createPersistencyBehavior() {
      return new EmptyDiagramPersistencyBehavior(this);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void registerBusinessObjectsListener() {
      super.registerBusinessObjectsListener();
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
            for (ISEDebugTarget target : observedTargets) {
               unobserveDebugTarget(target);
            }
            observedTargets.clear();
            Object[] bos = getDiagramTypeProvider().getFeatureProvider().getAllBusinessObjectsForPictogramElement(getDiagram());
            for (Object bo : bos) {
               if (bo instanceof ISEDebugTarget) {
                  ISEDebugTarget target = (ISEDebugTarget)bo;
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
   protected void unregisterBusinessObjectsListener() {
      super.unregisterBusinessObjectsListener();
      getDiagram().eAdapters().remove(diagramListener);
      DebugPlugin.getDefault().removeDebugEventListener(debugListener);
      SEDPreferenceUtil.getStore().removePropertyChangeListener(sedStorePropertyChangeListener );
      VisualizationPreferences.getStore().removePropertyChangeListener(visualizationStorePropertyChangeListener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ContextMenuProvider createContextMenuProvider() {
      return new CustomizableDiagramEditorContextMenuProvider(getDiagramContainer().getGraphicalViewer(),
                                                              getDiagramContainer().getActionRegistry(),
                                                              getConfigurationProvider(),
                                                              !isReadOnly(),
                                                              !isReadOnly());
   }
   
   /**
    * Handles the detected debug events. 
    * @param events The detected debug events.
    */
   protected void handleDebugEvents(DebugEvent[] events) {
      // Check if an update of the diagram is required.
      ISEDebugTarget[] targets = ExecutionTreeUtil.getAllDebugTargets(getDiagramTypeProvider());
      boolean updateRequired = false;
      int i = 0;
      while (!updateRequired && i < events.length) {
         if (DebugEvent.SUSPEND == events[i].getKind() ||
             DebugEvent.SUSPEND == events[i].getKind()) {
            if (events[i].getSource() instanceof IDebugElement) {
               IDebugTarget target = ((IDebugElement)events[i].getSource()).getDebugTarget();
               if (target instanceof ISEDebugTarget) {
                  updateRequired = ArrayUtil.contains(targets, target);
               }
            }
         }
         i++;
      }
      // Update diagram content if required.
      if (updateRequired) {
         // Do an asynchronous update in the UI thread (same behavior as DomainModelChangeListener which is responsible for changes in EMF objects)
         AbstractDependingOnObjectsJob.cancelJobs(diagramEditor);
         new AbstractDependingOnObjectsJob("Updating Symbolic Execution Tree", diagramEditor) {
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
            if (notificationService instanceof SENotificationService) {
               ((SENotificationService)notificationService).updatePictogramElements(elements, monitor);
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
    * Returns the shown {@link Diagram}.
    * @return The shown {@link Diagram}.
    */
   protected Diagram getDiagram() {
      IDiagramTypeProvider typeProvider = getDiagramTypeProvider();
      return typeProvider != null ? typeProvider.getDiagram() : null;
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
    * Checks if this editor is read-only or editable.
    * @return {@code true} read-only, {@code false} editable
    */
   public boolean isReadOnly() {
      return readOnly;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDirty() {
      return !isReadOnly() && super.isDirty();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void setPictogramElementsForSelection(PictogramElement[] pictogramElements) {
      super.setPictogramElementsForSelection(pictogramElements);
   }

   /**
    * Registers listeners on the given {@link ISEDebugTarget}.
    * @param target The {@link ISEDebugTarget} to observe.
    */
   protected void observeDebugTarget(ISEDebugTarget target) {
      if (target != null) {
         target.addAnnotationListener(targetListener);
         ISEAnnotation[] annotations = target.getRegisteredAnnotations();
         for (ISEAnnotation annotation : annotations) {
            observeAnnotation(annotation);
         }
      }
   }

   /**
    * Removes all listeners from the given {@link ISEDebugTarget}.
    * @param target The {@link ISEDebugTarget} to unobersve.
    */
   protected void unobserveDebugTarget(ISEDebugTarget target) {
      if (target != null) {
         target.removeAnnotationListener(targetListener);
         ISEAnnotation[] annotations = target.getRegisteredAnnotations();
         for (ISEAnnotation annotation : annotations) {
            unobserveAnnotation(annotation);
         }
      }
   }
   
   /**
    * Registers listeners on the given {@link ISEAnnotation}.
    * @param target The {@link ISEAnnotation} to observe.
    */
   protected void observeAnnotation(ISEAnnotation annotation) {
      annotation.addPropertyChangeListener(ISEAnnotation.PROP_ENABLED, annotationListener);
      annotation.addPropertyChangeListener(ISEAnnotation.PROP_HIGHLIGHT_BACKGROUND, annotationListener);
      annotation.addPropertyChangeListener(ISEAnnotation.PROP_BACKGROUND_COLOR, annotationListener);
      annotation.addPropertyChangeListener(ISEAnnotation.PROP_HIGHLIGHT_FOREGROUND, annotationListener);
      annotation.addPropertyChangeListener(ISEAnnotation.PROP_FOREGROUND_COLOR, annotationListener);
      annotation.addAnnotationLinkListener(annotationLinkListener);
   }
   
   /**
    * Removes all listeners from the given {@link ISEAnnotation}.
    * @param target The {@link ISEAnnotation} to unobersve.
    */
   protected void unobserveAnnotation(ISEAnnotation annotation) {
      annotation.removePropertyChangeListener(ISEAnnotation.PROP_ENABLED, annotationListener);
      annotation.removePropertyChangeListener(ISEAnnotation.PROP_HIGHLIGHT_BACKGROUND, annotationListener);
      annotation.removePropertyChangeListener(ISEAnnotation.PROP_BACKGROUND_COLOR, annotationListener);
      annotation.removePropertyChangeListener(ISEAnnotation.PROP_HIGHLIGHT_FOREGROUND, annotationListener);
      annotation.removePropertyChangeListener(ISEAnnotation.PROP_FOREGROUND_COLOR, annotationListener);
      annotation.removeAnnotationLinkListener(annotationLinkListener );
   }

   /**
    * When a new {@link ISEAnnotation} was added to an {@link ISEDebugTarget}.
    * @param e The event.
    */
   protected void handleAnnotationRegistered(SEAnnotationEvent e) {
      ISEAnnotation annotation = e.getAnnotation();
      observeAnnotation(annotation);
      if (annotation.isEnabled()) {
         updateStyle(annotation.listLinkTargets());
      }
   }

   /**
    * When an existing {@link ISEAnnotation} was removed from an {@link ISEDebugTarget}.
    * @param e The event.
    */
   protected void handleAnnotationUnregistered(SEAnnotationEvent e) {
      ISEAnnotation annotation = e.getAnnotation();
      unobserveAnnotation(annotation);
      if (annotation.isEnabled()) {
         updateStyle(annotation.listLinkTargets());
      }
   }

   /**
    * When an {@link ISEAnnotation} has moved on an {@link ISEDebugTarget}.
    * @param e The event.
    */
   protected void handleAnnotationMoved(SEAnnotationEvent e) {
      ISEAnnotation annotation = e.getAnnotation();
      if (annotation.isEnabled()) {
         updateStyle(annotation.listLinkTargets());
      }
   }

   /**
    * When a property of an {@link ISEAnnotation} has changed.
    * @param evt The event.
    */
   protected void handleAnnotationPropertyChange(PropertyChangeEvent evt) {
      ISEAnnotation annotation = (ISEAnnotation)evt.getSource();
      if (ISEAnnotation.PROP_ENABLED.equals(evt.getPropertyName())) {
         updateStyle(annotation.listLinkTargets());
      }
      else {
         if (annotation.isEnabled()) {
            updateStyle(annotation.listLinkTargets());
         }
      }
   }

   /**
    * When an {@link ISEAnnotationLink} was added to an {@link ISEAnnotation}.
    * @param e The event.
    */
   protected void handleAnnotationLinkAdded(SEAnnotationLinkEvent e) {
      if (e.getLink().getSource().isEnabled()) {
         updateStyle(Collections.singleton(e.getLink().getTarget()));
      }
   }

   /**
    * When an {@link ISEAnnotationLink} was removed from an {@link ISEAnnotation}.
    * @param e The event.
    */
   protected void handleAnnotationLinkRemoved(SEAnnotationLinkEvent e) {
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
         Set<ISENode> nodes = new HashSet<ISENode>();
         for (ISEDebugTarget target : observedTargets) {
            ISEAnnotation[] annotations = target.getRegisteredAnnotations();
            for (ISEAnnotation annotation : annotations) {
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
               ExecutionTreeStyleUtil.getStyleForDebugNode(new ISEAnnotation[0], diagram);
               ExecutionTreeStyleUtil.getStyleForDebugNodeText(new ISEAnnotation[0], diagram);
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
               ExecutionTreeStyleUtil.getStyleForDebugNodeText(new ISEAnnotation[0], diagram);
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
         if (!getDiagramContainer().getSite().getShell().isDisposed()) {
            getDiagramContainer().getSite().getShell().getDisplay().syncExec(new Runnable() {
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
    * representing one of the given {@link ISENode}s.
    * @param nodes The {@link ISENode}s to update the {@link Style}s of their {@link PictogramElement}s.
    */
   protected void updateStyle(Set<ISENode> nodes) {
      if (!nodes.isEmpty()) {
         boolean refreshRequired = false;
         IFeatureProvider fp = getDiagramTypeProvider().getFeatureProvider();
         for (ISENode node : nodes) {
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
         if (refreshRequired && !getDiagramContainer().getSite().getShell().isDisposed()) {
            getDiagramContainer().getSite().getShell().getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  refresh();
               }
            });
         }
      }
   }
}