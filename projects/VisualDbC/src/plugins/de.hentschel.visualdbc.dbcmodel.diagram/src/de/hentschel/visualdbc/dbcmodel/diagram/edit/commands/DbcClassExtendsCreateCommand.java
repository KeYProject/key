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
import org.eclipse.gmf.runtime.emf.type.core.commands.EditElementCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateRelationshipRequest;

import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbCBaseItemSemanticEditPolicy;

/**
 * @generated
 */
public class DbcClassExtendsCreateCommand extends EditElementCommand {

   /**
    * @generated
    */
   private final EObject source;

   /**
    * @generated
    */
   private final EObject target;

   /**
    * @generated
    */
   public DbcClassExtendsCreateCommand(CreateRelationshipRequest request,
         EObject source, EObject target) {
      super(request.getLabel(), null, request);
      this.source = source;
      this.target = target;
   }

   /**
    * @generated
    */
   public boolean canExecute() {
      if (source == null && target == null) {
         return false;
      }
      if (source != null && false == source instanceof DbcClass) {
         return false;
      }
      if (target != null && false == target instanceof DbcClass) {
         return false;
      }
      if (getSource() == null) {
         return true; // link creation is in progress; source is not defined yet
      }
      // target may be null here but it's possible to check constraint
      return DbCBaseItemSemanticEditPolicy.getLinkConstraints()
            .canCreateDbcClassExtends_4003(getSource(), getTarget());
   }

   /**
    * @generated
    */
   protected CommandResult doExecuteWithResult(IProgressMonitor monitor,
         IAdaptable info) throws ExecutionException {
      if (!canExecute()) {
         throw new ExecutionException(
               "Invalid arguments in create link command"); //$NON-NLS-1$
      }

      if (getSource() != null && getTarget() != null) {
         getSource().getExtends().add(getTarget());
      }
      return CommandResult.newOKCommandResult();

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
   protected DbcClass getSource() {
      return (DbcClass) source;
   }

   /**
    * @generated
    */
   protected DbcClass getTarget() {
      return (DbcClass) target;
   }
}