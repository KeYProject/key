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

package org.key_project.sed.ui.visualization.view;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.editparts.ZoomManager;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.CustomContext;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.editor.DiagramEditorInput;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.views.properties.IPropertySheetPage;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.sed.ui.visualization.execution_tree.editor.ExecutionTreeDiagramEditor;
import org.key_project.sed.ui.visualization.execution_tree.editor.ReadonlyDiagramEditorActionBarContributor;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugTargetConnectFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugTargetConnectFeature.IProgressHandler;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeFeatureProvider;
import org.key_project.sed.ui.visualization.util.EmptyDiagramPersistencyBehavior;
import org.key_project.util.eclipse.job.AbstractDependingOnObjectsJob;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.view.ParentBasedTabbedPropertySheetPage;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;

/**
 * This view shows the symbolic execution tree of selected {@link ISEDebugTarget}s
 * graphically as Graphiti diagram.
 * @author Martin Hentschel
 */
public class ExecutionTreeView extends AbstractLaunchViewBasedEditorInViewView<ExecutionTreeDiagramEditor, ReadonlyDiagramEditorActionBarContributor> {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.sed.ui.graphiti.view.ExecutionTreeView";
   
   /**
    * <p>
    * This flag is set to {@code true} during execution of {@link #handleDebugViewChanged(IDebugView, IDebugView)}
    * and set back to {@code false} during execution of {@link #handleEditorSelectionChanged(SelectionChangedEvent)}.
    * In this case no selection synchronization is done in {@link #handleEditorSelectionChanged(SelectionChangedEvent)}.
    * </p>
    * <p>
    * To skip the selection synchronization is important, because it is possible 
    * that the debug view and the diagram have different selections, e.g. if
    * a launch instance is selected in debug view. In this case is the diagram
    * selected represents the debug target instance.
    * </p>
    */
   private boolean internalSelectionUpdate = false;
   
   /**
    * The {@link ISelectionProvider} of the active {@link IWorkbenchPart} observed via {@link #editorSelectionListener}.
    */
   private ISelectionProvider observedSelectionProvider = null;
   
   /**
    * Listens for selection changes on {@link #getEditorPart()}.
    */
   private final ISelectionChangedListener editorSelectionListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleEditorSelectionChanged(event);
      }
   };
   
   /**
    * Listens for {@link Job} changes.
    */
   private final IJobChangeListener jobChangeListener = new JobChangeAdapter() {
      @Override
      public void done(IJobChangeEvent event) {
         handleJobDone(event);
      }
   };
   
   /**
    * Constructor.
    */
   public ExecutionTreeView() {
      Job.getJobManager().addJobChangeListener(jobChangeListener);
   }
   
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Class type) {
      if (type.equals(IPropertySheetPage.class)) {
         return new ParentBasedTabbedPropertySheetPage(this, getEditorPart());
      }
      else {
         return super.getAdapter(type);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ExecutionTreeDiagramEditor createEditorPart() {
      ExecutionTreeDiagramEditor editorPart = new ExecutionTreeDiagramEditor(true);
      editorPart.setDefaultSelectionSynchronizationEnabled(false);
      return editorPart;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void initActionBars(IViewSite viewSite, IActionBars actionBars) {
      // Nothing to do because the own ReadonlyDiagramEditorActionBarContributor is used.
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ReadonlyDiagramEditorActionBarContributor createEditorActionBarContributor() {
      return new ReadonlyDiagramEditorActionBarContributor(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void editorPartControlCreated(ExecutionTreeDiagramEditor editorPart, ReadonlyDiagramEditorActionBarContributor contributor) {
      observedSelectionProvider = editorPart.getSite().getSelectionProvider();
      if (observedSelectionProvider != null) { // TODO: Why is it null?
         observedSelectionProvider.addSelectionChangedListener(editorSelectionListener);
      }
      editorPart.setGridVisible(false);
      ZoomManager zoomManager = (ZoomManager)editorPart.getAdapter(ZoomManager.class);
      contributor.setZoomManager(zoomManager);
      super.editorPartControlCreated(editorPart, contributor);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected DiagramEditorInput createEditorInput() {
      return new DiagramEditorInput(EmptyDiagramPersistencyBehavior.EMPTY_DIAGRAM_URI, ExecutionTreeDiagramTypeProvider.PROVIDER_ID);
   }

   /**
    * When a {@link Job} terminates.
    * @param event The event.
    */
   protected void handleJobDone(IJobChangeEvent event) {
      handleEventToHandleNow();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isViewerUpdateInProgress() {
      return super.isViewerUpdateInProgress() || isJobInProgress();
   }
   
   /**
    * Checks if a {@link Job} is in progress.
    * @return {@code true} {@link Job} is in progress, {@code false} no {@link Job} is in progress.
    */
   protected boolean isJobInProgress() {
      Job[] diagramJobs = AbstractDependingOnObjectsJob.getJobs(getEditorPart());
      if (ArrayUtil.isEmpty(diagramJobs)) {
         Job[] debugJobs = AbstractDependingOnObjectsJob.getJobs(getDebugView());
         return !ArrayUtil.isEmpty(debugJobs);
      }
      else {
         return true;
      }
   }
   
   /**
    * When the selection on {@link #getEditorPart()} has changed.
    * @param event The event.
    */
   protected void handleEditorSelectionChanged(final SelectionChangedEvent event) {
      if (!isViewerUpdateInProgress()) {
         // Check if the selection changed was caused programmatically during synchronization or by the user.
         if (internalSelectionUpdate) {
            // Unset the internal flag to make sure that further selection changes
            // in the diagram are synchronized with the debug view.
            internalSelectionUpdate = false;
         }
         else {
            // List all selected business objects
            Object[] elements = SWTUtil.toArray(event.getSelection());
            final List<Object> businessObjects = new LinkedList<Object>();
            for (Object element : elements) {
               // Optional convert GMF instance to Graphiti instance
               if (element instanceof EditPart) {
                  element = ((EditPart)element).getModel();
               }
               // Optional convert Graphiti instance to model (ISEDDebugElement)
               if (element instanceof PictogramElement) {
                  element = getEditorPart().getDiagramTypeProvider().getFeatureProvider().getBusinessObjectForPictogramElement((PictogramElement)element);
               }
               businessObjects.add(element);
            }
            // Select in debug viewer
            SEDUIUtil.selectInDebugView(getEditorPart(), getDebugView(), businessObjects);
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isEditorAvailable() {
      ExecutionTreeDiagramEditor editor = getEditorPart();
      return editor != null && editor.getGraphicalViewer() != null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void doUpdateEditorContent(Set<ISEDebugTarget> oldTargets, 
                                        Set<ISEDebugTarget> newTargets, 
                                        Object[] newElements) {
      ExecutionTreeDiagramEditor editor = getEditorPart();
      // Make sure that the editor is already created; ignore event otherwise.
      if (editor != null && editor.getGraphicalViewer() != null) { 
         // Check if new targets are selected
         if (!CollectionUtil.containsSame(newTargets, oldTargets)) {
            // Check if a target was found
            if (!newTargets.isEmpty()) {
               // Set internal flag to indicate that the next selection change in diagram should be ignored.
               // This is required because the selection can be different, for instance if a launch instance is selected in debug view.
               // In this case is the diagram shown and the diagram itself is selected which has the debug target as business object.
               internalSelectionUpdate = true;
               editor.selectPictogramElements(new PictogramElement[0]); // If the unset is not executed multiple selection events are thrown during diagram recreation
               internalSelectionUpdate = true;
               // Recreate diagram
               final IDiagramTypeProvider typeProvider = editor.getDiagramTypeProvider();
               Assert.isNotNull(typeProvider);
               final IFeatureProvider featureProvider = typeProvider.getFeatureProvider();
               Assert.isTrue(featureProvider instanceof ExecutionTreeFeatureProvider);
               ICustomFeature feature = new DebugTargetConnectFeature((ExecutionTreeFeatureProvider)featureProvider);
               ICustomContext context = new CustomContext(new PictogramElement[] {typeProvider.getDiagram()});
               context.putProperty(DebugTargetConnectFeature.PROPERTY_DEBUG_TARGETS, newTargets.toArray(new ISEDebugTarget[newTargets.size()]));
               context.putProperty(DebugTargetConnectFeature.PROPERTY_ELEMENTS_TO_SELECT, newElements);
               context.putProperty(DebugTargetConnectFeature.PROPERTY_PROGRESS_HANDLER, new IProgressHandler() {
                  @Override
                  public void executionStarted(DebugTargetConnectFeature feature) {
                     setEditorEnabled(false);
                  }

                  @Override
                  public void executionFinished(DebugTargetConnectFeature feature) {
                     setEditorEnabled(true);
                  }
               });
               AbstractDependingOnObjectsJob.cancelJobs(editor);
               editor.executeFeatureInJob("Changing Symbolic Execution Tree", feature, context);
               // Unset message
               setMessage(null);
            }
            else {
               setMessage(MESSAGE_NO_DEBUG_TARGET_SELECTED);
            }
         }
         else {
            // Set internal flag to indicate that the next selection change in diagram should be ignored.
            // This is required because the selection can be different, for instance if a launch instance is selected in debug view.
            // In this case is the diagram shown and the diagram itself is selected which has the debug target as business object.
            internalSelectionUpdate = true;
            // Synchronize selection by selecting selected elements from debug view also in diagram editor
            editor.selectBusinessObjects(newElements);
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (observedSelectionProvider != null) {
         observedSelectionProvider.removeSelectionChangedListener(editorSelectionListener);
      }
      Job.getJobManager().removeJobChangeListener(jobChangeListener);
      getEditorPart().getSite().getSelectionProvider().removeSelectionChangedListener(editorSelectionListener);
      super.dispose();
   }
}