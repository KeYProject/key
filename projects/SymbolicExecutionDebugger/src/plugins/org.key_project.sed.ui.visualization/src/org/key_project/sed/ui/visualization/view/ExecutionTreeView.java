package org.key_project.sed.ui.visualization.view;

import java.util.LinkedHashSet;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
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
import org.key_project.sed.ui.visualization.execution_tree.editor.ExecutionTreeDiagramEditor;
import org.key_project.sed.ui.visualization.execution_tree.editor.ReadonlyDiagramEditorActionBarContributor;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugTargetConnectFeature;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeFeatureProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * This view shows the symbolic execution tree of selected {@link ISEDDebugTarget}s
 * graphically as Graphiti diagram.
 * @author Martin Hentschel
 */
public class ExecutionTreeView extends AbstractDebugViewBasedEditorInViewView<ExecutionTreeDiagramEditor, ReadonlyDiagramEditorActionBarContributor> {
   /**
    * The message which is shown to the user if the debug view is not opened.
    */
   public static final String MESSAGE_DEBUG_VIEW_NOT_OPENED = "View \"Debug\" is not opened.";

   /**
    * The message which is shown if no {@link ISEDDebugTarget} is selected.
    */
   private static final String MESSAGE_NO_DEBUG_TARGET_SELECTED = "No debug target is selected in View \"Debug\".";
  
   /**
    * Contains the shown debug targets.
    */
   private Set<ISEDDebugTarget> shownDebugTargets;
   
   /**
    * Listens for selection changes on {@link #getDebugView()}.
    */
   private ISelectionChangedListener debugViewSelectionListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleSelectionChanged(event);
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
      ExecutionTreeDiagramEditor editor = new ExecutionTreeDiagramEditor();
      editor.setReadOnly(true);
      editor.setPaletteHidden(true);
      return editor;
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
      ZoomManager zoomManager = (ZoomManager)editorPart.getAdapter(ZoomManager.class);
      contributor.setZoomManager(zoomManager);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected DiagramEditorInput createEditorInput() {
      // Create empty diagram
      final Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, 
                                                                          IOUtil.getFileNameWithoutExtension("Empty Diagram"), 
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
   protected void handleSelectionChanged(SelectionChangedEvent event) {
      // Make sure that event was provided by debug's viewer and not by something else what can happen if a maximized view is minimized.
      if (ObjectUtil.equals(event.getSource(), getDebugView().getViewer())) {
         // Update diagram
         updateDiagram(event.getSelection());
      }
   }
   
   /**
    * Updates the {@link Diagram} in a way that only {@link ISEDDebugTarget}
    * contained in the given {@link ISelection} are visible.
    * @param debugViewSelection The {@link ISelection} with the new {@link ISEDDebugTarget}s to show.
    */
   protected void updateDiagram(ISelection debugViewSelection) {
      try {
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
               ExecutionTreeDiagramEditor editor = getEditorPart();
               final IDiagramTypeProvider typeProvider = editor.getDiagramTypeProvider();
               Assert.isNotNull(typeProvider);
               final IFeatureProvider featureProvider = typeProvider.getFeatureProvider();
               Assert.isTrue(featureProvider instanceof ExecutionTreeFeatureProvider);
               ICustomFeature feature = new DebugTargetConnectFeature((ExecutionTreeFeatureProvider)featureProvider);
               ICustomContext context = new CustomContext(new PictogramElement[] {typeProvider.getDiagram()});
               context.putProperty(DebugTargetConnectFeature.PROPERTY_DEBUG_TARGETS, targets.toArray(new ISEDDebugTarget[targets.size()]));
               editor.executeFeatureInJob("Changing Symbolic Execution Tree", feature, context);
               // Unset message
               setMessage(null);
            }
            else {
               setMessage(MESSAGE_NO_DEBUG_TARGET_SELECTED);
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
      IDebugView debugView = getDebugView();
      if (debugView != null) {
         debugView.getSite().getSelectionProvider().removeSelectionChangedListener(debugViewSelectionListener);
      }
      super.dispose();
   }
}
