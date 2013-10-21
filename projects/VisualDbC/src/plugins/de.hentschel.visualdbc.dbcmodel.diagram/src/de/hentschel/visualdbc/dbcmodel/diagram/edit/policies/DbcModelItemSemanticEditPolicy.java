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

import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.emf.commands.core.commands.DuplicateEObjectsCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DuplicateElementsRequest;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcClassCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcEnumCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcInterfaceCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcPackageCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcProofCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcModelItemSemanticEditPolicy extends
      DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcModelItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcModel_1000);
   }

   /**
    * @generated
    */
   protected Command getCreateCommand(CreateElementRequest req) {
      if (DbCElementTypes.DbcPackage_2007 == req.getElementType()) {
         return getGEFWrapper(new DbcPackageCreateCommand(req));
      }
      if (DbCElementTypes.DbcInterface_2011 == req.getElementType()) {
         return getGEFWrapper(new DbcInterfaceCreateCommand(req));
      }
      if (DbCElementTypes.DbcClass_2012 == req.getElementType()) {
         return getGEFWrapper(new DbcClassCreateCommand(req));
      }
      if (DbCElementTypes.DbcEnum_2013 == req.getElementType()) {
         return getGEFWrapper(new DbcEnumCreateCommand(req));
      }
      if (DbCElementTypes.DbcProof_2014 == req.getElementType()) {
         return getGEFWrapper(new DbcProofCreateCommand(req));
      }
      return super.getCreateCommand(req);
   }

   /**
    * @generated
    */
   protected Command getDuplicateCommand(DuplicateElementsRequest req) {
      TransactionalEditingDomain editingDomain = ((IGraphicalEditPart) getHost())
            .getEditingDomain();
      return getGEFWrapper(new DuplicateAnythingCommand(editingDomain, req));
   }

   /**
    * @generated
    */
   private static class DuplicateAnythingCommand extends
         DuplicateEObjectsCommand {

      /**
       * @generated
       */
      public DuplicateAnythingCommand(TransactionalEditingDomain editingDomain,
            DuplicateElementsRequest req) {
         super(editingDomain, req.getLabel(), req.getElementsToBeDuplicated(),
               req.getAllDuplicatedElementsMap());
      }

   }

}