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

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.editparts.ZoomManager;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.CustomContext;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.ui.editor.DiagramEditorInput;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IViewSite;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.sed.ui.visualization.execution_tree.editor.ExecutionTreeDiagramEditor;
import org.key_project.sed.ui.visualization.execution_tree.editor.ReadonlyDiagramEditorActionBarContributor;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugTargetConnectFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugTargetConnectFeature.IProgressHandler;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeFeatureProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.job.AbstractWorkbenchPartJob;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * This view shows the symbolic execution tree of selected {@link ISEDDebugTarget}s
 * graphically as Graphiti diagram.
 * @author Martin Hentschel
 */
public class ExecutionTreeView extends AbstractDebugViewBasedEditorInViewView<ExecutionTreeDiagramEditor, ReadonlyDiagramEditorActionBarContributor> {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.sed.ui.graphiti.view.ExecutionTreeView";
   
   /**
    * The message which is shown to the user if the debug view is not opened.
    */
   public static final String MESSAGE_DEBUG_VIEW_NOT_OPENED = "View \"Debug\" is not opened.";

   /**
    * The message which is shown if no {@link ISEDDebugTarget} is selected.
    */
   private static final String MESSAGE_NO_DEBUG_TARGET_SELECTED = "No symbolic debug target is selected in View \"Debug\".";
  
   /**
    * Contains the shown debug targets.
    */
   private Set<ISEDDebugTarget> shownDebugTargets;
   
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
    * Listens for selection changes on {@link #getEditorPart()}.
    */
   private ISelectionChangedListener editorSelectionListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleEditorSelectionChanged(event);
      }
   };
   
   /**
    * Listens for selection changes on {@link #getDebugView()}.
    */
   private ISelectionChangedListener debugViewSelectionListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleDebugViewSelectionChanged(event);
      }
   };
   
   /**
    * Constructor.
    */
   public ExecutionTreeView() {
      setMessage(MESSAGE_DEBUG_VIEW_NOT_OPENED);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ExecutionTreeDiagramEditor createEditorPart() {
      ExecutionTreeDiagramEditor editorPart = new ExecutionTreeDiagramEditor();
      editorPart.setDefaultSelectionSynchronizationEnabled(false);
      editorPart.setReadOnly(true);
      editorPart.setPaletteHidden(true);
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
      editorPart.getSite().getSelectionProvider().addSelectionChangedListener(editorSelectionListener);
      editorPart.setGridVisible(false);
      ZoomManager zoomManager = (ZoomManager)editorPart.getAdapter(ZoomManager.class);
      contributor.setZoomManager(zoomManager);
      if (getDebugView() != null) {
         updateDiagram(getDebugView().getViewer().getSelection());
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected DiagramEditorInput createEditorInput() {
      // Create empty diagram
      Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, 
                                                                    "Empty Diagram", 
                                                                    true);
      URI domainURI = URI.createURI("INVALID" + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT);
      GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, domainURI.toString());
      // Create editing domain and resource that contains the diagram
      TransactionalEditingDomain domain = ExecutionTreeUtil.createDomainAndResource(diagram);
      return DiagramEditorInput.createEditorInput(diagram, domain, ExecutionTreeDiagramTypeProvider.PROVIDER_ID, true);
   }

   /**
    * When the selection on {@link #getDebugView()} has changed.
    * @param event The event.
    */
   protected void handleDebugViewSelectionChanged(SelectionChangedEvent event) {
      // Make sure that event was provided by debug's viewer and not by something else what can happen if a maximized view is minimized.
      if (ObjectUtil.equals(event.getSource(), getDebugView().getViewer())) {
         // Update diagram
         updateDiagram(event.getSelection());
      }
   }
   
   /**
    * When the selection on {@link #getEditorPart()} has changed.
    * @param event The event.
    */
   protected void handleEditorSelectionChanged(final SelectionChangedEvent event) {
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
   
   /**
    * Updates the {@link Diagram} in a way that only {@link ISEDDebugTarget}
    * contained in the given {@link ISelection} are visible.
    * @param debugViewSelection The {@link ISelection} with the new {@link ISEDDebugTarget}s to show.
    */
   protected void updateDiagram(ISelection debugViewSelection) {
      try {
         ExecutionTreeDiagramEditor editor = getEditorPart();
         // Make sure that the editor is already created; ignore event otherwise.
         if (editor != null && editor.getGraphicalViewer() != null) { 
            // Collect ISEDDebugTargets to show
            final Set<ISEDDebugTarget> targets = new LinkedHashSet<ISEDDebugTarget>();
            Object[] elements = SWTUtil.toArray(debugViewSelection);
            for (Object element : elements) {
               if (element instanceof ISEDDebugElement) {
                  targets.add(((ISEDDebugElement)element).getDebugTarget());
               }
               else if (element instanceof ILaunch) {
                  IDebugTarget[] launchTargets = ((ILaunch)element).getDebugTargets();
                  for (IDebugTarget target : launchTargets) {
                     if (target instanceof ISEDDebugTarget) {
                        targets.add((ISEDDebugTarget)target);
                     }
                  }
               }
            }
            // Check if new targets are selected
            if (!CollectionUtil.containsSame(targets, shownDebugTargets)) {
               // Check if a target was found
               shownDebugTargets = targets;
               if (!targets.isEmpty()) {
                  // Set internal flag to indicate that the next selection change in diagram should be ignored.
                  // This is required because the selection can be different, for instance if a launch instance is selected in debug view.
                  // In this case is the diagram shown and the diagram itself is selected which has the debug target as business object.
                  internalSelectionUpdate = true;
                  editor.selectPictogramElements(new PictogramElement[0]); // If the unset is not executed multiple selection events are thrown during diagram recreation
                  internalSelectionUpdate = true;
                  // Recrate diagram
                  final IDiagramTypeProvider typeProvider = editor.getDiagramTypeProvider();
                  Assert.isNotNull(typeProvider);
                  final IFeatureProvider featureProvider = typeProvider.getFeatureProvider();
                  Assert.isTrue(featureProvider instanceof ExecutionTreeFeatureProvider);
                  ICustomFeature feature = new DebugTargetConnectFeature((ExecutionTreeFeatureProvider)featureProvider);
                  ICustomContext context = new CustomContext(new PictogramElement[] {typeProvider.getDiagram()});
                  context.putProperty(DebugTargetConnectFeature.PROPERTY_DEBUG_TARGETS, targets.toArray(new ISEDDebugTarget[targets.size()]));
                  context.putProperty(DebugTargetConnectFeature.PROPERTY_ELEMENTS_TO_SELECT, elements);
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
                  AbstractWorkbenchPartJob.cancelJobs(editor);
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
               editor.selectBusinessObjects(elements);
            }
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getSite().getShell(), e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleDebugView(IDebugView debugView) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(debugView.getSite().getId());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleDebugViewChanged(IDebugView oldDebugView, IDebugView newDebugView) {
      // Cleanup old view
      if (oldDebugView != null) {
         oldDebugView.getSite().getSelectionProvider().removeSelectionChangedListener(debugViewSelectionListener);
      }
      // Handle new view
      if (newDebugView != null) {
         newDebugView.getSite().getSelectionProvider().addSelectionChangedListener(debugViewSelectionListener);
         setMessage(MESSAGE_NO_DEBUG_TARGET_SELECTED);
         updateDiagram(getDebugView().getSite().getSelectionProvider().getSelection());
      }
      else {
         setMessage(MESSAGE_DEBUG_VIEW_NOT_OPENED);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      getEditorPart().getSite().getSelectionProvider().removeSelectionChangedListener(editorSelectionListener);
      IDebugView debugView = getDebugView();
      if (debugView != null) {
         debugView.getSite().getSelectionProvider().removeSelectionChangedListener(debugViewSelectionListener);
      }
      super.dispose();
   }
}