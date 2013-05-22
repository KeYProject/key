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

package de.hentschel.visualdbc.dbcmodel.diagram.edit.commands;

import java.util.Map;

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
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateRelationshipRequest;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbCBaseItemSemanticEditPolicy;

/**
 * @generated
 */
public class DbcProofReferenceCreateCommand extends EditElementCommand {

   /**
    * @generated
    */
   private final EObject source;

   /**
    * @generated
    */
   private final EObject target;

   // Begin Changes MHE
   /**
    * @generated NOT
    */
   @SuppressWarnings("rawtypes")
   private Map extendedData;

   // End Changes MHE   

   /**
    * @generated NOT
    */
   public DbcProofReferenceCreateCommand(CreateRelationshipRequest request,
         EObject source, EObject target) {
      super(request.getLabel(), null, request);
      this.source = source;
      this.target = target;
      // Begin Changes MHE
      this.extendedData = request.getParameters();
      // End Changes MHE
   }

   /**
    * @generated
    */
   public boolean canExecute() {
      if (source == null && target == null) {
         return false;
      }
      if (source != null && false == source instanceof DbcProof) {
         return false;
      }
      if (target != null && false == target instanceof IDbCProofReferencable) {
         return false;
      }
      if (getSource() == null) {
         return true; // link creation is in progress; source is not defined yet
      }
      // target may be null here but it's possible to check constraint
      return DbCBaseItemSemanticEditPolicy.getLinkConstraints()
            .canCreateDbcProofReference_4002(getSource(), getTarget());
   }

   /**
    * @generated NOT
    */
   protected CommandResult doExecuteWithResult(IProgressMonitor monitor,
         IAdaptable info) throws ExecutionException {
      if (!canExecute()) {
         throw new ExecutionException(
               "Invalid arguments in create link command"); //$NON-NLS-1$
      }

      DbcProofReference newElement = DbcmodelFactory.eINSTANCE
            .createDbcProofReference();
      // Begin Changes MHE
      if (extendedData != null) {
         Object kind = extendedData
               .get(DbcmodelPackage.Literals.DBC_PROOF_REFERENCE__KIND);
         if (kind != null) {
            newElement.setKind(kind.toString());
         }
      }
      // End Changes MHE
      getSource().getProofReferences().add(newElement);
      newElement.setTarget(getTarget());
      doConfigure(newElement, monitor, info);
      ((CreateElementRequest) getRequest()).setNewElement(newElement);
      return CommandResult.newOKCommandResult(newElement);

   }

   /**
    * @generated
    */
   protected void doConfigure(DbcProofReference newElement,
         IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
      IElementType elementType = ((CreateElementRequest) getRequest())
            .getElementType();
      ConfigureRequest configureRequest = new ConfigureRequest(
            getEditingDomain(), newElement, elementType);
      configureRequest.setClientContext(((CreateElementRequest) getRequest())
            .getClientContext());
      configureRequest.addParameters(getRequest().getParameters());
      configureRequest.setParameter(CreateRelationshipRequest.SOURCE,
            getSource());
      configureRequest.setParameter(CreateRelationshipRequest.TARGET,
            getTarget());
      ICommand configureCommand = elementType.getEditCommand(configureRequest);
      if (configureCommand != null && configureCommand.canExecute()) {
         configureCommand.execute(monitor, info);
      }
   }

   /**
    * @generated
    */
   protected void setElementToEdit(EObject element) {
      throw new UnsupportedOperationException();
   }

   /**
    * @generated
    */
   protected DbcProof getSource() {
      return (DbcProof) source;
   }

   /**
    * @generated
    */
   protected IDbCProofReferencable getTarget() {
      return (IDbCProofReferencable) target;
   }

}