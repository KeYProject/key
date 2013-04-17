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

package de.hentschel.visualdbc.dbcmodel.diagram.edit.policies;

import java.util.Iterator;
import org.eclipse.emf.ecore.EAnnotation;
import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.diagram.core.commands.DeleteCommand;
import org.eclipse.gmf.runtime.emf.commands.core.command.CompositeTransactionalCommand;
import org.eclipse.gmf.runtime.emf.type.core.commands.DestroyElementCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateRelationshipRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyElementRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.ReorientRelationshipRequest;
import org.eclipse.gmf.runtime.notation.Edge;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcProofReferenceCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcProofReferenceReorientCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcEnumLiteralItemSemanticEditPolicy extends
      DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcEnumLiteralItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcEnumLiteral_3020);
   }

   /**
    * @generated
    */
   protected Command getDestroyElementCommand(DestroyElementRequest req) {
      View view = (View) getHost().getModel();
      CompositeTransactionalCommand cmd = new CompositeTransactionalCommand(
            getEditingDomain(), null);
      cmd.setTransactionNestingEnabled(false);
      for (Iterator<?> it = view.getTargetEdges().iterator(); it.hasNext();) {
         Edge incomingLink = (Edge) it.next();
         if (DbCVisualIDRegistry.getVisualID(incomingLink) == DbcProofReferenceEditPart.VISUAL_ID) {
            DestroyElementRequest r = new DestroyElementRequest(
                  incomingLink.getElement(), false);
            cmd.add(new DestroyElementCommand(r));
            cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
            continue;
         }
      }
      EAnnotation annotation = view.getEAnnotation("Shortcut"); //$NON-NLS-1$
      if (annotation == null) {
         // there are indirectly referenced children, need extra commands: false
         addDestroyShortcutsCommand(cmd, view);
         // delete host element
         cmd.add(new DestroyElementCommand(req));
      }
      else {
         cmd.add(new DeleteCommand(getEditingDomain(), view));
      }
      return getGEFWrapper(cmd.reduce());
   }

   /**
    * @generated
    */
   protected Command getCreateRelationshipCommand(CreateRelationshipRequest req) {
      Command command = req.getTarget() == null ? getStartCreateRelationshipCommand(req)
            : getCompleteCreateRelationshipCommand(req);
      return command != null ? command : super
            .getCreateRelationshipCommand(req);
   }

   /**
    * @generated
    */
   protected Command getStartCreateRelationshipCommand(
         CreateRelationshipRequest req) {
      if (DbCElementTypes.DbcProofReference_4002 == req.getElementType()) {
         return null;
      }
      return null;
   }

   /**
    * @generated
    */
   protected Command getCompleteCreateRelationshipCommand(
         CreateRelationshipRequest req) {
      if (DbCElementTypes.DbcProofReference_4002 == req.getElementType()) {
         return getGEFWrapper(new DbcProofReferenceCreateCommand(req,
               req.getSource(), req.getTarget()));
      }
      return null;
   }

   /**
    * Returns command to reorient EClass based link. New link target or source
    * should be the domain model element associated with this node.
    * 
    * @generated
    */
   protected Command getReorientRelationshipCommand(
         ReorientRelationshipRequest req) {
      switch (getVisualID(req)) {
      case DbcProofReferenceEditPart.VISUAL_ID:
         return getGEFWrapper(new DbcProofReferenceReorientCommand(req));
      }
      return super.getReorientRelationshipCommand(req);
   }

}