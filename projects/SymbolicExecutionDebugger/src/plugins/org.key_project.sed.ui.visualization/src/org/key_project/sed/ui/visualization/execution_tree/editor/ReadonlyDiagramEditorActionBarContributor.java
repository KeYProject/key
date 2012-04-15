package org.key_project.sed.ui.visualization.execution_tree.editor;

import org.eclipse.gef.ui.actions.ActionBarContributor;
import org.eclipse.gef.ui.actions.GEFActionConstants;
import org.eclipse.gef.ui.actions.ZoomComboContributionItem;
import org.eclipse.gef.ui.actions.ZoomInRetargetAction;
import org.eclipse.gef.ui.actions.ZoomOutRetargetAction;
import org.eclipse.graphiti.platform.IPlatformImageConstants;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.eclipse.graphiti.ui.editor.DiagramEditorActionBarContributor;
import org.eclipse.graphiti.ui.internal.Messages;
import org.eclipse.graphiti.ui.internal.action.SaveImageAction;
import org.eclipse.graphiti.ui.internal.action.UpdateAction;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.actions.RetargetAction;

/**
 * Contains a subset of the provided actions of {@link DiagramEditorActionBarContributor}
 * which are useful for a read-only usage of {@link DiagramEditor}s.
 * @author Martin Hentschel
 * @see DiagramEditorActionBarContributor
 */
// TODO: Disable contributions if a message is shown in the ExecutionTreeView
@SuppressWarnings("restriction")
public class ReadonlyDiagramEditorActionBarContributor extends ActionBarContributor {
   /**
    * {@inheritDoc}
    */
   @Override
   protected void buildActions() {
      addAction(ActionFactory.SAVE_AS.create(PlatformUI.getWorkbench().getActiveWorkbenchWindow()));

      addRetargetAction((RetargetAction) ActionFactory.PRINT.create(PlatformUI.getWorkbench().getActiveWorkbenchWindow()));
      addRetargetAction((RetargetAction) ActionFactory.SELECT_ALL.create(PlatformUI.getWorkbench().getActiveWorkbenchWindow()));
      
      addRetargetAction(new ZoomInRetargetAction());
      addRetargetAction(new ZoomOutRetargetAction());
      addRetargetAction(new RetargetAction(GEFActionConstants.TOGGLE_GRID_VISIBILITY, Messages.DiagramEditorActionBarContributor_Grid, IAction.AS_CHECK_BOX));
      
      RetargetAction updateRetargetAction = new RetargetAction(UpdateAction.ACTION_ID, UpdateAction.TEXT);
      updateRetargetAction.setImageDescriptor(GraphitiUi.getImageService().getImageDescriptorForId(IPlatformImageConstants.IMG_EDIT_REFRESH));
      updateRetargetAction.setActionDefinitionId(UpdateAction.ACTION_DEFINITION_ID);
      addRetargetAction(updateRetargetAction);
      RetargetAction saveImageRetargetAction = new RetargetAction(SaveImageAction.ACTION_ID, SaveImageAction.TEXT);
      saveImageRetargetAction.setActionDefinitionId(SaveImageAction.ACTION_DEFINITION_ID);
      addRetargetAction(saveImageRetargetAction);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void declareGlobalActionKeys() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void contributeToToolBar(IToolBarManager tbm) {
      tbm.add(getAction(ActionFactory.SAVE_AS.getId()));
      tbm.add(new Separator());

      tbm.add(getAction(ActionFactory.PRINT.getId()));
      tbm.add(new Separator());
      
      tbm.add(getAction(GEFActionConstants.ZOOM_OUT));
      tbm.add(getAction(GEFActionConstants.ZOOM_IN));
      ZoomComboContributionItem zoomCombo = new ZoomComboContributionItem(getPage());
      tbm.add(zoomCombo);
      tbm.add(new Separator());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void contributeToMenu(IMenuManager menubar) {
      super.contributeToMenu(menubar);

      MenuManager viewMenu = new MenuManager(Messages.GraphicsActionBarContributor_0_xmen);
      viewMenu.add(getAction(GEFActionConstants.ZOOM_IN));
      viewMenu.add(getAction(GEFActionConstants.ZOOM_OUT));
      viewMenu.add(getAction(GEFActionConstants.TOGGLE_GRID_VISIBILITY));
      menubar.add(viewMenu);

      menubar.add(new Separator());
      menubar.add(getAction(ActionFactory.SAVE_AS.getId()));

      menubar.add(new Separator());
      menubar.add(getAction(SaveImageAction.ACTION_ID));
      menubar.add(getAction(ActionFactory.PRINT.getId()));
   }
}
