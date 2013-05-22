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

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gmf.runtime.common.core.command.CommandResult;
import org.eclipse.gmf.runtime.emf.type.core.commands.EditElementCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.ReorientRelationshipRequest;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbCBaseItemSemanticEditPolicy;

/**
 * @generated
 */
public class DbcProofReferenceReorientCommand extends EditElementCommand {

   /**
    * @generated
    */
   private final int reorientDirection;

   /**
    * @generated
    */
   private final EObject oldEnd;

   /**
    * @generated
    */
   private final EObject newEnd;

   /**
    * @generated
    */
   public DbcProofReferenceReorientCommand(ReorientRelationshipRequest request) {
      super(request.getLabel(), request.getRelationship(), request);
      reorientDirection = request.getDirection();
      oldEnd = request.getOldRelationshipEnd();
      newEnd = request.getNewRelationshipEnd();
   }

   /**
    * @generated
    */
   public boolean canExecute() {
      if (false == getElementToEdit() instanceof DbcProofReference) {
         return false;
      }
      if (reorientDirection == ReorientRelationshipRequest.REORIENT_SOURCE) {
         return canReorientSource();
      }
      if (reorientDirection == ReorientRelationshipRequest.REORIENT_TARGET) {
         return canReorientTarget();
      }
      return false;
   }

   /**
    * @generated
    */
   protected boolean canReorientSource() {
      if (!(oldEnd instanceof DbcProof && newEnd instanceof DbcProof)) {
         return false;
      }
      IDbCProofReferencable target = getLink().getTarget();
      return DbCBaseItemSemanticEditPolicy.getLinkConstraints()
            .canExistDbcProofReference_4002(getLink(), getNewSource(), target);
   }

   /**
    * @generated
    */
   protected boolean canReorientTarget() {
      if (!(oldEnd instanceof IDbCProofReferencable && newEnd instanceof IDbCProofReferencable)) {
         return false;
      }
      if (!(getLink().eContainer() instanceof DbcProof)) {
         return false;
      }
      DbcProof source = (DbcProof) getLink().eContainer();
      return DbCBaseItemSemanticEditPolicy.getLinkConstraints()
            .canExistDbcProofReference_4002(getLink(), source, getNewTarget());
   }

   /**
    * @generated
    */
   protected CommandResult doExecuteWithResult(IProgressMonitor monitor,
         IAdaptable info) throws ExecutionException {
      if (!canExecute()) {
         throw new ExecutionException(
               "Invalid arguments in reorient link command"); //$NON-NLS-1$
      }
      if (reorientDirection == ReorientRelationshipRequest.REORIENT_SOURCE) {
         return reorientSource();
      }
      if (reorientDirection == ReorientRelationshipRequest.REORIENT_TARGET) {
         return reorientTarget();
      }
      throw new IllegalStateException();
   }

   /**
    * @generated
    */
   protected CommandResult reorientSource() throws ExecutionException {
      getOldSource().getProofReferences().remove(getLink());
      getNewSource().getProofReferences().add(getLink());
      return CommandResult.newOKCommandResult(getLink());
   }

   /**
    * @generated
    */
   protected CommandResult reorientTarget() throws ExecutionException {
      getLink().setTarget(getNewTarget());
      return CommandResult.newOKCommandResult(getLink());
   }

   /**
    * @generated
    */
   protected DbcProofReference getLink() {
      return (DbcProofReference) getElementToEdit();
   }

   /**
    * @generated
    */
   protected DbcProof getOldSource() {
      return (DbcProof) oldEnd;
   }

   /**
    * @generated
    */
   protected DbcProof getNewSource() {
      return (DbcProof) newEnd;
   }

   /**
    * @generated
    */
   protected IDbCProofReferencable getOldTarget() {
      return (IDbCProofReferencable) oldEnd;
   }

   /**
    * @generated
    */
   protected IDbCProofReferencable getNewTarget() {
      return (IDbCProofReferencable) newEnd;
   }
}