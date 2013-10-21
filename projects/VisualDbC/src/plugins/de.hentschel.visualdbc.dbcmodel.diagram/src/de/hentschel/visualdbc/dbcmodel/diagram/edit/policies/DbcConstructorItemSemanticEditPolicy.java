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
import org.eclipse.gmf.runtime.common.core.command.ICompositeCommand;
import org.eclipse.gmf.runtime.diagram.core.commands.DeleteCommand;
import org.eclipse.gmf.runtime.emf.commands.core.command.CompositeTransactionalCommand;
import org.eclipse.gmf.runtime.emf.type.core.commands.DestroyElementCommand;
import org.eclipse.gmf.runtime.emf.type.core.commands.DestroyReferenceCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateRelationshipRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyElementRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyReferenceRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.ReorientReferenceRelationshipRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.ReorientRelationshipRequest;
import org.eclipse.gmf.runtime.notation.Edge;
import org.eclipse.gmf.runtime.notation.Node;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcProofReferenceCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcProofReferenceReorientCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcProofTargetCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcProofTargetReorientCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorDbcConstructorCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProof2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofTargetEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcConstructorItemSemanticEditPolicy extends
      DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcConstructorItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcConstructor_3010);
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
         if (DbCVisualIDRegistry.getVisualID(incomingLink) == DbcProofTargetEditPart.VISUAL_ID) {
            DestroyReferenceRequest r = new DestroyReferenceRequest(
                  incomingLink.getSource().getElement(), null, incomingLink
                        .getTarget().getElement(), false);
            cmd.add(new DestroyReferenceCommand(r));
            cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
            continue;
         }
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
         addDestroyChildNodesCommand(cmd);
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
   private void addDestroyChildNodesCommand(ICompositeCommand cmd) {
      View view = (View) getHost().getModel();
      for (Iterator<?> nit = view.getChildren().iterator(); nit.hasNext();) {
         Node node = (Node) nit.next();
         switch (DbCVisualIDRegistry.getVisualID(node)) {
         case DbcConstructorDbcConstructorCompartmentEditPart.VISUAL_ID:
            for (Iterator<?> cit = node.getChildren().iterator(); cit.hasNext();) {
               Node cnode = (Node) cit.next();
               switch (DbCVisualIDRegistry.getVisualID(cnode)) {
               case DbcProof2EditPart.VISUAL_ID:
                  for (Iterator<?> it = cnode.getSourceEdges().iterator(); it
                        .hasNext();) {
                     Edge outgoingLink = (Edge) it.next();
                     if (DbCVisualIDRegistry.getVisualID(outgoingLink) == DbcProofTargetEditPart.VISUAL_ID) {
                        DestroyReferenceRequest r = new DestroyReferenceRequest(
                              outgoingLink.getSource().getElement(), null,
                              outgoingLink.getTarget().getElement(), false);
                        cmd.add(new DestroyReferenceCommand(r));
                        cmd.add(new DeleteCommand(getEditingDomain(),
                              outgoingLink));
                        continue;
                     }
                     if (DbCVisualIDRegistry.getVisualID(outgoingLink) == DbcProofReferenceEditPart.VISUAL_ID) {
                        DestroyElementRequest r = new DestroyElementRequest(
                              outgoingLink.getElement(), false);
                        cmd.add(new DestroyElementCommand(r));
                        cmd.add(new DeleteCommand(getEditingDomain(),
                              outgoingLink));
                        continue;
                     }
                  }
                  cmd.add(new DestroyElementCommand(new DestroyElementRequest(
                        getEditingDomain(), cnode.getElement(), false))); // directlyOwned: true
                  // don't need explicit deletion of cnode as parent's view deletion would clean child views as well 
                  // cmd.add(new org.eclipse.gmf.runtime.diagram.core.commands.DeleteCommand(getEditingDomain(), cnode));
                  break;
               case DbcOperationContractEditPart.VISUAL_ID:
                  for (Iterator<?> it = cnode.getTargetEdges().iterator(); it
                        .hasNext();) {
                     Edge incomingLink = (Edge) it.next();
                     if (DbCVisualIDRegistry.getVisualID(incomingLink) == DbcProofTargetEditPart.VISUAL_ID) {
                        DestroyReferenceRequest r = new DestroyReferenceRequest(
                              incomingLink.getSource().getElement(), null,
                              incomingLink.getTarget().getElement(), false);
                        cmd.add(new DestroyReferenceCommand(r));
                        cmd.add(new DeleteCommand(getEditingDomain(),
                              incomingLink));
                        continue;
                     }
                     if (DbCVisualIDRegistry.getVisualID(incomingLink) == DbcProofReferenceEditPart.VISUAL_ID) {
                        DestroyElementRequest r = new DestroyElementRequest(
                              incomingLink.getElement(), false);
                        cmd.add(new DestroyElementCommand(r));
                        cmd.add(new DeleteCommand(getEditingDomain(),
                              incomingLink));
                        continue;
                     }
                  }
                  cmd.add(new DestroyElementCommand(new DestroyElementRequest(
                        getEditingDomain(), cnode.getElement(), false))); // directlyOwned: true
                  // don't need explicit deletion of cnode as parent's view deletion would clean child views as well 
                  // cmd.add(new org.eclipse.gmf.runtime.diagram.core.commands.DeleteCommand(getEditingDomain(), cnode));
                  break;
               }
            }
            break;
         }
      }
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
      if (DbCElementTypes.DbcProofTarget_4001 == req.getElementType()) {
         return null;
      }
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
      if (DbCElementTypes.DbcProofTarget_4001 == req.getElementType()) {
         return getGEFWrapper(new DbcProofTargetCreateCommand(req,
               req.getSource(), req.getTarget()));
      }
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

   /**
    * Returns command to reorient EReference based link. New link target or source
    * should be the domain model element associated with this node.
    * 
    * @generated
    */
   protected Command getReorientReferenceRelationshipCommand(
         ReorientReferenceRelationshipRequest req) {
      switch (getVisualID(req)) {
      case DbcProofTargetEditPart.VISUAL_ID:
         return getGEFWrapper(new DbcProofTargetReorientCommand(req));
      }
      return super.getReorientReferenceRelationshipCommand(req);
   }

}