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

package org.key_project.sed.ui.visualization.util;

import org.eclipse.gef.EditPartViewer;
import org.eclipse.gef.ui.actions.ActionRegistry;
import org.eclipse.graphiti.ui.editor.DiagramEditorContextMenuProvider;
import org.eclipse.graphiti.ui.internal.action.UpdateAction;
import org.eclipse.graphiti.ui.internal.config.IConfigurationProvider;
import org.eclipse.jface.action.IMenuManager;

/**
 * An extended version of {@link DiagramEditorContextMenuProvider} which
 * allows to disable the undo/redo group.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class CustomizableDiagramEditorContextMenuProvider extends DiagramEditorContextMenuProvider {
   /**
    * Undo/redo group available?
    */
   private boolean undoGroupAvailable;
   
   /**
    * Update action available?
    */
   private boolean updateActionAvailable;

   /**
    * Constructor.
    * @param viewer The EditPartViewer, for which the context-menu shall be displayed.
    * @param registry The action-registry, which contains the actions corresponding to the menu-items.
    * @param configurationProvider the configuration provider
    * @param undoGroupAvailable {@code true} undo/redo group is available, {@code false} undo/redo group is not available.
    * @param updateActionAvailable {@code true} update action is available in context menu, {@code false} update action is not available in context menu.
    */
   public CustomizableDiagramEditorContextMenuProvider(EditPartViewer viewer, 
                                                       ActionRegistry registry, 
                                                       IConfigurationProvider configurationProvider, 
                                                       boolean undoGroupAvailable,
                                                       boolean updateActionAvailable) {
      super(viewer, registry, configurationProvider);
      this.undoGroupAvailable = undoGroupAvailable;
      this.updateActionAvailable = updateActionAvailable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void addDefaultMenuGroupUndo(IMenuManager manager) {
      if (isUndoGroupAvailable()) {
         super.addDefaultMenuGroupUndo(manager);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override   
   protected void addActionToMenuIfAvailable(IMenuManager manager, String actionId, String menuGroup) {
      if (UpdateAction.ACTION_ID.equals(actionId)) {
         if (isUpdateActionAvailable()) {
            super.addActionToMenuIfAvailable(manager, actionId, menuGroup);
         }
      }
      else {
         super.addActionToMenuIfAvailable(manager, actionId, menuGroup);
      }
   }

   /**
    * Checks if the undo/redo group is available or not.
    * @return {@code true} undo/redo group is available, {@code false} undo/redo group is not available.
    */
   public boolean isUndoGroupAvailable() {
      return undoGroupAvailable;
   }

   /**
    * Checks if the update action is available or not.
    * @return {@code true} update action is available in context menu, {@code false} update action is not available in context menu.
    */
   public boolean isUpdateActionAvailable() {
      return updateActionAvailable;
   }
}