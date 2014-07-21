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

package de.hentschel.visualdbc.dbcmodel.diagram.edit.commands;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gmf.runtime.common.core.command.CommandResult;
import org.eclipse.gmf.runtime.common.core.command.ICommand;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.emf.type.core.commands.EditElementCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.ConfigureRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * @generated
 */
public class DbcAttributeCreateCommand extends EditElementCommand {

   /**
    * @generated
    */
   public DbcAttributeCreateCommand(CreateElementRequest req) {
      super(req.getLabel(), null, req);
   }

   /**
    * FIXME: replace with setElementToEdit()
    * @generated
    */
   protected EObject getElementToEdit() {
      EObject container = ((CreateElementRequest) getRequest()).getContainer();
      if (container instanceof View) {
         container = ((View) container).getElement();
      }
      return container;
   }

   /**
    * @generated
    */
   public boolean canExecute() {
      return true;

   }

   /**
    * @generated
    */
   protected CommandResult doExecuteWithResult(IProgressMonitor monitor,
         IAdaptable info) throws ExecutionException {
      DbcAttribute newElement = DbcmodelFactory.eINSTANCE.createDbcAttribute();

      AbstractDbcInterface owner = (AbstractDbcInterface) getElementToEdit();
      owner.getAttributes().add(newElement);

      doConfigure(newElement, monitor, info);

      ((CreateElementRequest) getRequest()).setNewElement(newElement);
      return CommandResult.newOKCommandResult(newElement);
   }

   /**
    * @generated
    */
   protected void doConfigure(DbcAttribute newElement,
         IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
      IElementType elementType = ((CreateElementRequest) getRequest())
            .getElementType();
      ConfigureRequest configureRequest = new ConfigureRequest(
            getEditingDomain(), newElement, elementType);
      configureRequest.setClientContext(((CreateElementRequest) getRequest())
            .getClientContext());
      configureRequest.addParameters(getRequest().getParameters());
      ICommand configureCommand = elementType.getEditCommand(configureRequest);
      if (configureCommand != null && configureCommand.canExecute()) {
         configureCommand.execute(monitor, info);
      }
   }

}