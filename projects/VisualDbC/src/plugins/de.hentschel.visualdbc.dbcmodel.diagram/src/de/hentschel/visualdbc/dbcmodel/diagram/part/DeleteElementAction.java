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

package de.hentschel.visualdbc.dbcmodel.diagram.part;

import java.util.Iterator;
import java.util.List;

import org.eclipse.gef.EditPart;
import org.eclipse.gef.Request;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.commands.UnexecutableCommand;
import org.eclipse.gmf.runtime.diagram.ui.actions.AbstractDeleteFromAction;
import org.eclipse.gmf.runtime.diagram.ui.actions.ActionIds;
import org.eclipse.gmf.runtime.diagram.ui.commands.CommandProxy;
import org.eclipse.gmf.runtime.diagram.ui.commands.ICommandProxy;
import org.eclipse.gmf.runtime.diagram.ui.l10n.DiagramUIMessages;
import org.eclipse.gmf.runtime.emf.commands.core.command.CompositeTransactionalCommand;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;

/**
 * @generated
 */
public class DeleteElementAction extends AbstractDeleteFromAction {

   /**
    * @generated
    */
   public DeleteElementAction(IWorkbenchPart part) {
      super(part);
   }

   /**
    * @generated
    */
   public DeleteElementAction(IWorkbenchPage workbenchPage) {
      super(workbenchPage);
   }

   /**
    * @generated
    */
   public void init() {
      super.init();
      setId(ActionIds.ACTION_DELETE_FROM_MODEL);
      setText(DiagramUIMessages.DiagramEditor_Delete_from_Model);
      setToolTipText(DiagramUIMessages.DiagramEditor_Delete_from_ModelToolTip);
      ISharedImages workbenchImages = PlatformUI.getWorkbench()
            .getSharedImages();
      setHoverImageDescriptor(workbenchImages
            .getImageDescriptor(ISharedImages.IMG_TOOL_DELETE));
      setImageDescriptor(workbenchImages
            .getImageDescriptor(ISharedImages.IMG_TOOL_DELETE));
      setDisabledImageDescriptor(workbenchImages
            .getImageDescriptor(ISharedImages.IMG_TOOL_DELETE_DISABLED));
   }

   /**
    * @generated
    */
   protected String getCommandLabel() {
      return DiagramUIMessages.DiagramEditor_Delete_from_Model;
   }

   /**
    * @generated
    */
   protected Command getCommand(Request request) {
      List operationSet = getOperationSet();
      if (operationSet.isEmpty()) {
         return UnexecutableCommand.INSTANCE;
      }
      Iterator editParts = operationSet.iterator();
      CompositeTransactionalCommand command = new CompositeTransactionalCommand(
            getEditingDomain(), getCommandLabel());
      while (editParts.hasNext()) {
         EditPart editPart = (EditPart) editParts.next();
         Command curCommand = editPart.getCommand(request);
         if (curCommand != null) {
            command.compose(new CommandProxy(curCommand));
         }
      }
      if (command.isEmpty() || command.size() != operationSet.size()) {
         return UnexecutableCommand.INSTANCE;
      }
      return new ICommandProxy(command);
   }
}