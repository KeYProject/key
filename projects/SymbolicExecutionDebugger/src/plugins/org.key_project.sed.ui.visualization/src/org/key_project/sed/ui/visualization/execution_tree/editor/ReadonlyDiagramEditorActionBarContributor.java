/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

import org.eclipse.gef.editparts.ZoomManager;
import org.eclipse.gef.ui.actions.GEFActionConstants;
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
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.actions.RetargetAction;
import org.key_project.sed.ui.visualization.action.AbstractEditorInViewActionBarContributor;
import org.key_project.sed.ui.visualization.action.GlobalEnablementZoomComboContributionItem;
import org.key_project.sed.ui.visualization.util.GraphitiGlobalEnablementWrapperAction;
import org.key_project.util.eclipse.view.editorInView.GlobalEnablementWrapperAction;
import org.key_project.util.eclipse.view.editorInView.SaveAsAction;

/**
 * Contains a subset of the provided actions of {@link DiagramEditorActionBarContributor}
 * which are useful for a read-only usage of {@link DiagramEditor}s.
 * @author Martin Hentschel
 * @see DiagramEditorActionBarContributor
 */
@SuppressWarnings("restriction")
public class ReadonlyDiagramEditorActionBarContributor extends AbstractEditorInViewActionBarContributor {
   /**
    * The {@link ZoomManager} which should be always used independent
    * of the provided {@link ZoomManager} of the active {@link IWorkbenchPart}.
    */
   private ZoomManager zoomManager;
   
   /**
    * The provided {@link GlobalEnablementZoomComboContributionItem}.
    */
   private GlobalEnablementZoomComboContributionItem zoomCombo;

   /**
    * Constructor.
    * @param fixedPart The fixed {@link IWorkbenchPart} which should always be used as source in {@link RetargetAction}s.
    */
   public ReadonlyDiagramEditorActionBarContributor(IWorkbenchPart fixedPart) {
      super(fixedPart);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected GlobalEnablementWrapperAction createActionWrapper(IAction action) {
      return new GraphitiGlobalEnablementWrapperAction(action);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void buildActions() {
      addAction(new SaveAsAction(getFixedPart()));

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
      zoomCombo = new GlobalEnablementZoomComboContributionItem(getPage());
      zoomCombo.setFixedZoomManager(zoomManager);
      registerGlobalEnablement(zoomCombo);
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
   
   /**
    * Sets the {@link ZoomManager} which should be always used independent
    * of the provided {@link ZoomManager} of the active {@link IWorkbenchPart}.
    * @param zoomManager The {@link ZoomManager} to use.
    */
   public void setZoomManager(ZoomManager zoomManager) {
      this.zoomManager = zoomManager;
      if (zoomCombo != null) {
         zoomCombo.setFixedZoomManager(zoomManager);
      }
   }
}