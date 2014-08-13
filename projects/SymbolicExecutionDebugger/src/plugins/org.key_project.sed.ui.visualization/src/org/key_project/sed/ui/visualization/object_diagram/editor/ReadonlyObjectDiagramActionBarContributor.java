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

package org.key_project.sed.ui.visualization.object_diagram.editor;

import org.eclipse.gef.ui.actions.ActionBarContributor;
import org.eclipse.gef.ui.actions.GEFActionConstants;
import org.eclipse.gef.ui.actions.ZoomComboContributionItem;
import org.eclipse.gef.ui.actions.ZoomInRetargetAction;
import org.eclipse.gef.ui.actions.ZoomOutRetargetAction;
import org.eclipse.graphiti.platform.IPlatformImageConstants;
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
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.actions.RetargetAction;

/**
 * Modified copy of {@link DiagramEditorActionBarContributor} which provides
 * only read-only actions and not the actions which modifies the shown diagram.
 * It is also enhances with the "save as" action.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class ReadonlyObjectDiagramActionBarContributor extends ActionBarContributor {
   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Modified copy of {@link DiagramEditorActionBarContributor#buildActions()}.
    * </p>
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
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Modified copy of {@link DiagramEditorActionBarContributor#contributeToToolBar(IToolBarManager)}.
    * </p>
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
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Modified copy of {@link DiagramEditorActionBarContributor#contributeToMenu(IMenuManager)}.
    * </p>
    */
   @Override
   public void contributeToMenu(IMenuManager menubar) {
      super.contributeToMenu(menubar);

      MenuManager viewMenu = new MenuManager(Messages.GraphicsActionBarContributor_0_xmen);
      viewMenu.add(getAction(GEFActionConstants.ZOOM_IN));
      viewMenu.add(getAction(GEFActionConstants.ZOOM_OUT));
      viewMenu.add(getAction(GEFActionConstants.TOGGLE_GRID_VISIBILITY));
      menubar.insertAfter(IWorkbenchActionConstants.M_EDIT, viewMenu);

      IMenuManager fileMenu = menubar.findMenuUsingPath(IWorkbenchActionConstants.M_FILE);
      if (fileMenu != null) {
         // Might not be available in RCP case
         fileMenu.insertAfter(ActionFactory.EXPORT.getId(), getAction(SaveImageAction.ACTION_ID));
      }
   }
}