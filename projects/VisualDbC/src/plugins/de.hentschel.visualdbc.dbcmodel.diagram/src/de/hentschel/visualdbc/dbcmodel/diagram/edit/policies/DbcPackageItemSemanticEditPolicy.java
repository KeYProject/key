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
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyElementRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyReferenceRequest;
import org.eclipse.gmf.runtime.notation.Edge;
import org.eclipse.gmf.runtime.notation.Node;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.AbstractDbcClassImplementsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClass2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassExtendsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnum2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterface2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceExtendsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackage2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageDbcPackageCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProof2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofTargetEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcPackageItemSemanticEditPolicy extends
      DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcPackageItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcPackage_2007);
   }

   /**
    * @generated
    */
   protected Command getDestroyElementCommand(DestroyElementRequest req) {
      View view = (View) getHost().getModel();
      CompositeTransactionalCommand cmd = new CompositeTransactionalCommand(
            getEditingDomain(), null);
      cmd.setTransactionNestingEnabled(false);
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
         case DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID:
            for (Iterator<?> cit = node.getChildren().iterator(); cit.hasNext();) {
               Node cnode = (Node) cit.next();
               switch (DbCVisualIDRegistry.getVisualID(cnode)) {
               case DbcPackage2EditPart.VISUAL_ID:
                  cmd.add(new DestroyElementCommand(new DestroyElementRequest(
                        getEditingDomain(), cnode.getElement(), false))); // directlyOwned: true
                  // don't need explicit deletion of cnode as parent's view deletion would clean child views as well 
                  // cmd.add(new org.eclipse.gmf.runtime.diagram.core.commands.DeleteCommand(getEditingDomain(), cnode));
                  break;
               case DbcClass2EditPart.VISUAL_ID:
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
                     if (DbCVisualIDRegistry.getVisualID(incomingLink) == DbcClassExtendsEditPart.VISUAL_ID) {
                        DestroyReferenceRequest r = new DestroyReferenceRequest(
                              incomingLink.getSource().getElement(), null,
                              incomingLink.getTarget().getElement(), false);
                        cmd.add(new DestroyReferenceCommand(r));
                        cmd.add(new DeleteCommand(getEditingDomain(),
                              incomingLink));
                        continue;
                     }
                  }
                  for (Iterator<?> it = cnode.getSourceEdges().iterator(); it
                        .hasNext();) {
                     Edge outgoingLink = (Edge) it.next();
                     if (DbCVisualIDRegistry.getVisualID(outgoingLink) == DbcClassExtendsEditPart.VISUAL_ID) {
                        DestroyReferenceRequest r = new DestroyReferenceRequest(
                              outgoingLink.getSource().getElement(), null,
                              outgoingLink.getTarget().getElement(), false);
                        cmd.add(new DestroyReferenceCommand(r));
                        cmd.add(new DeleteCommand(getEditingDomain(),
                              outgoingLink));
                        continue;
                     }
                     if (DbCVisualIDRegistry.getVisualID(outgoingLink) == AbstractDbcClassImplementsEditPart.VISUAL_ID) {
                        DestroyReferenceRequest r = new DestroyReferenceRequest(
                              outgoingLink.getSource().getElement(), null,
                              outgoingLink.getTarget().getElement(), false);
                        cmd.add(new DestroyReferenceCommand(r));
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
               case DbcInterface2EditPart.VISUAL_ID:
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
                     if (DbCVisualIDRegistry.getVisualID(incomingLink) == DbcInterfaceExtendsEditPart.VISUAL_ID) {
                        DestroyReferenceRequest r = new DestroyReferenceRequest(
                              incomingLink.getSource().getElement(), null,
                              incomingLink.getTarget().getElement(), false);
                        cmd.add(new DestroyReferenceCommand(r));
                        cmd.add(new DeleteCommand(getEditingDomain(),
                              incomingLink));
                        continue;
                     }
                     if (DbCVisualIDRegistry.getVisualID(incomingLink) == AbstractDbcClassImplementsEditPart.VISUAL_ID) {
                        DestroyReferenceRequest r = new DestroyReferenceRequest(
                              incomingLink.getSource().getElement(), null,
                              incomingLink.getTarget().getElement(), false);
                        cmd.add(new DestroyReferenceCommand(r));
                        cmd.add(new DeleteCommand(getEditingDomain(),
                              incomingLink));
                        continue;
                     }
                  }
                  for (Iterator<?> it = cnode.getSourceEdges().iterator(); it
                        .hasNext();) {
                     Edge outgoingLink = (Edge) it.next();
                     if (DbCVisualIDRegistry.getVisualID(outgoingLink) == DbcInterfaceExtendsEditPart.VISUAL_ID) {
                        DestroyReferenceRequest r = new DestroyReferenceRequest(
                              outgoingLink.getSource().getElement(), null,
                              outgoingLink.getTarget().getElement(), false);
                        cmd.add(new DestroyReferenceCommand(r));
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
               case DbcEnum2EditPart.VISUAL_ID:
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
                  for (Iterator<?> it = cnode.getSourceEdges().iterator(); it
                        .hasNext();) {
                     Edge outgoingLink = (Edge) it.next();
                     if (DbCVisualIDRegistry.getVisualID(outgoingLink) == AbstractDbcClassImplementsEditPart.VISUAL_ID) {
                        DestroyReferenceRequest r = new DestroyReferenceRequest(
                              outgoingLink.getSource().getElement(), null,
                              outgoingLink.getTarget().getElement(), false);
                        cmd.add(new DestroyReferenceCommand(r));
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
               }
            }
            break;
         }
      }
   }

}