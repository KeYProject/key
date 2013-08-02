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
import org.eclipse.gmf.runtime.emf.type.core.requests.ReorientReferenceRelationshipRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.ReorientRelationshipRequest;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbCBaseItemSemanticEditPolicy;

/**
 * @generated
 */
public class DbcProofTargetReorientCommand extends EditElementCommand {

   /**
    * @generated
    */
   private final int reorientDirection;

   /**
    * @generated
    */
   private final EObject referenceOwner;

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
   public DbcProofTargetReorientCommand(
         ReorientReferenceRelationshipRequest request) {
      super(request.getLabel(), null, request);
      reorientDirection = request.getDirection();
      referenceOwner = request.getReferenceOwner();
      oldEnd = request.getOldRelationshipEnd();
      newEnd = request.getNewRelationshipEnd();
   }

   /**
    * @generated
    */
   public boolean canExecute() {
      if (false == referenceOwner instanceof DbcProof) {
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
      if (!(oldEnd instanceof IDbCProvable && newEnd instanceof DbcProof)) {
         return false;
      }
      return DbCBaseItemSemanticEditPolicy.getLinkConstraints()
            .canExistDbcProofTarget_4001(getNewSource(), getOldTarget());
   }

   /**
    * @generated
    */
   protected boolean canReorientTarget() {
      if (!(oldEnd instanceof IDbCProvable && newEnd instanceof IDbCProvable)) {
         return false;
      }
      return DbCBaseItemSemanticEditPolicy.getLinkConstraints()
            .canExistDbcProofTarget_4001(getOldSource(), getNewTarget());
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
      getOldSource().setTarget(null);
      getNewSource().setTarget(getOldTarget());
      return CommandResult.newOKCommandResult(referenceOwner);
   }

   /**
    * @generated
    */
   protected CommandResult reorientTarget() throws ExecutionException {
      getOldSource().setTarget(getNewTarget());
      return CommandResult.newOKCommandResult(referenceOwner);
   }

   /**
    * @generated
    */
   protected DbcProof getOldSource() {
      return (DbcProof) referenceOwner;
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
   protected IDbCProvable getOldTarget() {
      return (IDbCProvable) oldEnd;
   }

   /**
    * @generated
    */
   protected IDbCProvable getNewTarget() {
      return (IDbCProvable) newEnd;
   }
}